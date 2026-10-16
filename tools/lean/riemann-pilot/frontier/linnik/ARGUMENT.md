# Linnik's constant from a zero-free half-plane and a zero-density estimate

README round 519. This is a paper argument. Nothing in it is machine-checked, and it has not been refereed. Section 8 records how it was checked.

## 1. Statement

**Notation.** For `q ≥ 1`, `X(q)` is the set of Dirichlet characters mod `q`, and `χ₀` is the principal one. For `χ ∈ X(q)`, `Z(χ)` is the multiset of zeros `ρ = β + iγ` of `L(s, χ)` with `0 < β < 1`. For an imprimitive `χ`, `L(s, χ)` is the primitive `L(s, χ*)` times finitely many Euler factors `1 − χ*(p)p^{−s}`, whose zeros lie on `Re s = 0`, so `Z(χ) = Z(χ*)`. For `1/2 ≤ σ ≤ 1` and `T ≥ 2`,

```
N(σ, T; q) = Σ_{χ ∈ X(q)} #{ρ ∈ Z(χ) : β ≥ σ, |γ| ≤ T}.
```

**Hypotheses.**

- **(H1) at `θ₀`, a zero-free half-plane.** For every `q ≥ 1`, every `χ ∈ X(q)` and every `s` with `Re s > θ₀`, `L(s, χ) ≠ 0`; for `χ = χ₀`, `s ≠ 1`.
- **(H2) at `(A, B)`, a zero-density estimate over the characters of one modulus.** There is `C ≥ 1` such that `N(σ, T; q) ≤ C (qT)^{A(1−σ)} (log qT)^B` for every `q ≥ 1`, `T ≥ 2` and `1/2 ≤ σ ≤ 1`.

**Theorem.** Assume (H1) at some `θ₀ < 1` and (H2) at some `(A, B)` with `A ≥ 2`. For every `η ∈ (0, 1]` there is `q₀` such that, for every `q ≥ q₀` and every `a` prime to `q`, there is a prime `p ≡ a (mod q)` with `q^{A+η} ≤ p ≤ 2q^{A+η}`. So the least such prime satisfies `p(q, a) ≪_η q^{A+η}` for every `q`. The implied constant is effective when the constants of (H2) are; (H1) enters only as a statement that zeros are absent.

**Instances.**

| (H1) | (H2) | exponent `L` | status of the inputs |
|---|---|---|---|
| `θ₀ = 11/12`: `Eis.LFunction_ne_zero_of_re_gt` | `A = 12/5`: Huxley (1974/75) | `12/5 + η` | (H1) kernel-checked in this stack; (H2) published |
| `θ₀ = 11/12` | `A = 7/3`: Chen–Gupta–Li (2025) | `7/3 + η` | (H2) a preprint, not checked here |
| `θ₀ = 11/12` | `A = 1 + 2θ₀ = 17/6`: round 518's route over the characters mod `q` | `17/6 + η` | (H2) not proved; section 7 |
| `θ₀ = 7/8`: the release | `A = 12/5` | `12/5 + η` | (H1) the release's claim, not checked here |

For comparison: Xylouris proved `L = 5` (2011); Naslund claims `3.99` (2026, a preprint); the generalized Riemann hypothesis gives `2 + η`. Section 6 has the sources.

**Without (H2).** The proof below with the trivial count `Σ_χ x^{σ_χ} ≤ φ(q)x^{θ₀}` in place of 3.9 gives `L = 1/(1 − θ₀) + η`: `12 + η` at `θ₀ = 11/12`, which is STRUCTURAL-REVIEW's K2.

## 2. Why it works

The zeros with real part about `σ` contribute about `(q^A/x)^{1−σ}` to the count of primes up to `x` in a class mod `q`, where `A` is the density exponent. Classically there can be zeros with `1 − σ` as small as `c/log q`. At `x = q^L` such a zero contributes `exp(−c(L − A))`, a constant rather than a small quantity. The unconditional proofs control these zeros with the zero-free region, log-free density estimates and the Deuring–Heilbronn phenomenon, and reach exponents of about `5`. Under (H1), `1 − σ ≥ 1 − θ₀` for every zero, so every contribution is at most `q^{−(L−A)(1−θ₀)}`, and any `L > A` works.

## 3. Proof

**3.1 Parameters.** Fix `η ∈ (0, 1]` and put

- `δ₁ = η/(2A)`, `T = q^{δ₁}`, `x = q^{A+η}`;
- `δ = η(1 − θ₀)/(4(A + η))`, so `0 < δ ≤ (1 − θ₀)/12` (as `η ≤ 1 ≤ A/2`) and `θ₀ + δ < 1`;
- `k = ⌈2 + 2A/η⌉`;
- `w`: a smooth function on `(0, ∞)` with support in `[1, 2]`, `0 ≤ w ≤ 1`, `w ≢ 0`, and `ŵ(s) = ∫₀^∞ w(u)u^{s−1} du`.

`ŵ` is entire and `ŵ(1) > 0`. Integrating by parts `j` times, `ŵ(s) = (−1)^j/(s(s+1)···(s+j−1)) · ∫ w^{(j)}(u)u^{s+j−1} du`, so `|ŵ(s)| ≤ c_j(1 + |Im s|)^{−j}` on `−1 ≤ Re s ≤ 3`, with `c_j` depending only on `w` and `j`. Below, `q ≥ q₀` is large enough for each "large `q`" statement, and `c` is a constant depending only on `θ₀, A, B, C, η, w` (not the same at each occurrence).

**3.2 Mellin inversion.** For `χ ∈ X(q)` let `F_χ = −L′/L(·, χ)`, which equals `Σ_n Λ(n)χ(n)n^{−s}` on `Re s > 1`. Then

```
S_χ(x) := Σ_n Λ(n)χ(n)w(n/x) = (1/2πi) ∫_{(2)} F_χ(s) ŵ(s) x^s ds,
```

with absolute convergence: `|F_χ(2 + it)| ≤ −ζ′/ζ(2)` and `|ŵ(2 + it)| ≤ c₂(1 + |t|)^{−2}`.

**3.3 The principal character.** `S_{χ₀}(x) = Σ_n Λ(n)w(n/x) − Σ_{p | q} Σ_{m ≥ 1} log p · w(p^m/x)`. For each `p` at most two `m` have `x ≤ p^m ≤ 2x`, so the second sum is at most `2 log q`. (H1) for `ζ` (the case `q = 1`) gives `Σ_n Λ(n)w(n/x) = x ŵ(1) + O(x^{θ₀+δ})`, by the same line shift as 3.6 for `−ζ′/ζ` with the residue `x ŵ(1)` at `s = 1`; the log-derivative bound near `s = 1` is applied to `(s − 1)ζ(s)`. So `S_{χ₀}(x) ≥ x ŵ(1) − c x^{θ₀+δ} − 2 log q`.

**3.4 A zero-free region for each character.** For `χ ≠ χ₀` let

```
σ_χ = max({1/2} ∪ {β : ρ ∈ Z(χ), |γ| ≤ 2T}),
```

a maximum over a finite set. By (H1), `σ_χ ≤ θ₀`. `L(s, χ)` is entire with no zero in `D_χ = {Re s > σ_χ, |Im s| < 2T} ∪ {Re s > θ₀}`. Its zeros with `0 < Re s < 1` and `|Im s| < 2T` have `Re s ≤ σ_χ`, it has no zero on `Re s ≥ 1`, and its other zeros have `Re s ≤ 0`.

**3.5 The log-derivative in `D_χ`.** Let `χ ≠ χ₀`. For `s` with either (a) `σ_χ + δ ≤ Re s ≤ 2` and `|Im s| ≤ T`, or (b) `θ₀ + δ ≤ Re s ≤ 2`:

```
|F_χ(s)| ≤ (48/δ²) log(10q(|Im s| + 5)).     (∗)
```

*Proof.* Put `s₁ = 2 + i Im s` and `r = |s − s₁| = 2 − Re s`. Put `R = 2 − σ_χ − δ/2` in case (a) and `R = 2 − θ₀ − δ/2` in case (b), so that `R − r ≥ δ/2` and `R ≤ 3/2`. The last uses `σ_χ ≥ 1/2` in case (a) and `θ₀ ≥ 1/2` in case (b): the zeros of a primitive `L(s, χ)` are symmetric under `ρ ↦ 1 − ρ̄`, so (H1) forces `θ₀ ≥ 1/2`.

- *The disc is zero-free.* The disc `|z − s₁| ≤ R` lies in `Re z ≥ σ_χ + δ/2` in case (a) and in `Re z ≥ θ₀ + δ/2` in case (b). In case (a) it also lies in `|Im z| ≤ T + 3/2 < 2T` (`T > 3/2` for large `q`). So it lies in `D_χ`, and `h(z) = log L(z, χ) − log L(s₁, χ)` is holomorphic on it, with `h(s₁) = 0`.
- *An upper bound on the disc.* There `1/2 ≤ Re z ≤ 7/2`. For `Re z ≥ 3/2`, `|L(z, χ)| ≤ ζ(3/2) < 3`. For `1/2 ≤ Re z ≤ 3/2`, partial summation with `|Σ_{n≤u} χ(n)| ≤ q` and `N = q(|z| + 1)` gives `|L(z, χ)| ≤ 2√N + (1 + 2|z|)q N^{−1/2} ≤ 5(q(|z| + 1))^{1/2}`, with `|z| ≤ |Im z| + 3/2`.
- *A lower bound at the centre.* `|L(s₁, χ)| ≥ Π_p(1 + p^{−2})^{−1} = ζ(4)/ζ(2) > 1/2`.
- *So `Re h` is bounded.* On the disc, `Re h ≤ M := log(10q(|Im s| + 5))`, using `|Im z| ≤ |Im s| + 3/2`.
- *Borel–Carathéodory.* It gives `|h(w)| ≤ 2r′M/(R − r′)` for `|w − s₁| ≤ r′ < R`. Apply it on the circle of radius `(R − r)/2` around `s`, where `r′ = (R + r)/2`, and then Cauchy's estimate: `|h′(s)| ≤ 8MR/(R − r)² ≤ 48M/δ²`.

`h′ = L′/L(·, χ)`, so (∗) follows. ∎

**3.6 Moving the line.** For `χ ≠ χ₀`, `Γ_χ` is the following path, taken upward:

- the ray `{θ₀ + δ + it : t ≤ −T}`;
- the horizontal segment `[θ₀ + δ − iT, σ_χ + δ − iT]`;
- the vertical segment `[σ_χ + δ − iT, σ_χ + δ + iT]`;
- the horizontal segment `[σ_χ + δ + iT, θ₀ + δ + iT]`;
- the ray `{θ₀ + δ + it : t ≥ T}`.

The closed region between `Re s = 2` and `Γ_χ` lies in `D_χ`, so `F_χ(s)ŵ(s)x^s` is holomorphic on it. On the horizontal segments `[θ₀ + δ ± iU, 2 ± iU]` it is at most `c δ^{−2} log(qU) U^{−k} x²` by (∗) in case (b). Cauchy's theorem on rectangles, letting `U → ∞`, gives

```
S_χ(x) = (1/2πi) ∫_{Γ_χ} F_χ(s) ŵ(s) x^s ds.
```

**3.7 Bounding the integral.** On `Γ_χ`, `|x^s| ≤ x^{σ_χ+δ}` on the vertical segment and `|x^s| ≤ x^{θ₀+δ}` elsewhere (`x ≥ 1`). Use (∗) in case (a) on the three segments and in case (b) on the rays, `|ŵ| ≤ c₂(1 + |Im s|)^{−2}` on the vertical segment, and `|ŵ| ≤ c_k(1 + |Im s|)^{−k}` elsewhere. The horizontal segments have length `θ₀ − σ_χ ≤ 1/2`. So:

- the vertical segment contributes at most `c δ^{−2} log(qT) x^{σ_χ+δ}`;
- the horizontal segments, at most `c δ^{−2} log(qT) x^{θ₀+δ} T^{−k}`;
- the rays, at most `c δ^{−2} x^{θ₀+δ} ∫_T^∞ log(10q(t + 5))(1 + t)^{−k} dt ≤ c δ^{−2} log(qT) x^{θ₀+δ} T^{1−k}`.

Hence

```
|S_χ(x)| ≤ c δ^{−2} log(qT) (x^{σ_χ+δ} + x^{θ₀+δ} T^{1−k})   for χ ≠ χ₀.     (∗∗)
```

**3.8 Orthogonality.** For `(a, q) = 1`,

```
S(x) := Σ_{n ≡ a (mod q)} Λ(n)w(n/x) = φ(q)^{−1} Σ_{χ ∈ X(q)} χ̄(a) S_χ(x) ≥ φ(q)^{−1} (S_{χ₀}(x) − Σ_{χ ≠ χ₀} |S_χ(x)|).
```

**3.9 Counting the characters by `σ_χ`.** For each `χ ≠ χ₀`, `x^{σ_χ} = x^{1/2} + ∫_{1/2}^{σ_χ} x^σ log x dσ`. If `1/2 ≤ σ < σ_χ`, then `σ_χ > 1/2`, so `χ` has a zero with `β = σ_χ > σ` and `|γ| ≤ 2T`. Hence `#{χ ≠ χ₀ : σ_χ > σ} ≤ N(σ, 2T; q)`. Summing over `χ`, and using `σ_χ ≤ θ₀` and (H2):

```
Σ_{χ≠χ₀} x^{σ_χ} ≤ φ(q) x^{1/2} + log x ∫_{1/2}^{θ₀} x^σ N(σ, 2T; q) dσ
              ≤ φ(q) x^{1/2} + C x log x (log 2qT)^B · max_{1/2 ≤ σ ≤ θ₀} ((2qT)^A/x)^{1−σ}.
```

**3.10 Sizes.** By 3.1:

- `(2qT)^A/x = 2^A q^{Aδ₁ − η} = 2^A q^{−η/2} ≤ 1` for large `q`, so the maximum in 3.9 is at most `(2^A q^{−η/2})^{1−θ₀}`, attained at `σ = θ₀`;
- `x^δ = q^{(A+η)δ} = q^{η(1−θ₀)/4}`.

By (∗∗), 3.9, and `log(qT)`, `log x`, `log 2qT ≤ c log q`:

```
Σ_{χ≠χ₀} |S_χ(x)| ≤ c δ^{−2} log q · [x^δ φ(q) x^{1/2} + x^δ x (log q)^{B+1} q^{−η(1−θ₀)/2} + φ(q) x^{θ₀+δ} T^{1−k}].
```

Divided by `x`, the three terms in the bracket are:

- `φ(q) x^{δ−1/2} ≤ q^{1 − (A+η)/2 + η(1−θ₀)/4} ≤ q^{−η/4}`, using `A ≥ 2`;
- `(log q)^{B+1} q^{η(1−θ₀)/4 − η(1−θ₀)/2} = (log q)^{B+1} q^{−η(1−θ₀)/4}`;
- `φ(q) x^{θ₀+δ−1} T^{1−k} ≤ q^{1 − δ₁(k−1)} ≤ q^{−η/(2A)}`, as `θ₀ + δ < 1` and `δ₁(k − 1) ≥ 1 + η/(2A)`.

So `Σ_{χ≠χ₀} |S_χ(x)| ≤ x ŵ(1)/4` for large `q`. With 3.3 and 3.8, `S(x) ≥ x ŵ(1)/(2φ(q))`.

**3.11 Primes.** In `S(x)`, the terms with `n = p^m`, `m ≥ 2`, total at most `Σ_{2 ≤ m ≤ log₂ 2x} θ((2x)^{1/m}) ≤ 4 log₂(2x)(2x)^{1/2}`, by Chebyshev's `θ(y) ≤ 2y` and `w ≤ 1`. This is at most `x ŵ(1)/(4φ(q))` for large `q`, since `x^{1/2} = q^{(A+η)/2} ≥ q^{1+η/2}`. So the primes `p ≡ a (mod q)` in `[x, 2x]` give `Σ log p · w(p/x) ≥ x ŵ(1)/(4φ(q)) > 0`, and at least one exists. ∎

## 4. The parameter check

`params.py` checks, in exact rationals, the exponent inequalities that 3.1, 3.10 and 3.11 use, for the five instances `(A, θ₀) = (12/5, 11/12), (7/3, 11/12), (17/6, 11/12), (12/5, 7/8), (11/4, 7/8)` and `η = 1, 1/10, 1/100, 1/1000`. All 20 cases pass. It checks arithmetic only, not the analysis.

## 5. Inputs and sources

- **(H1) at `11/12`.** `Eis.LFunction_ne_zero_of_re_gt` (`src/DirichletCharHalfPlane.lean:207`, rounds 492–495). Its docstring reads: "for every modulus `q ≥ 1`, every Dirichlet character `χ` mod `q` and every `s` with `Re s > 11/12`, `L(s, χ) ≠ 0`, the trivial character excepted at `s = 1`." Its axioms are `propext`, `Classical.choice` and `Quot.sound`. It is only as strong as the faithfulness of its statement (round 466's note on `riemannZeta` and `DirichletCharacter.LFunction` applies).
- **(H2) at `12/5`.** M. N. Huxley, "Large values of Dirichlet polynomials. III", Acta Arith. 26 (1974/75), 435–444, which was not read here. It is read as quoted by Banks and Shparlinski (arXiv:1605.07553v2, section 3; symbols decoded from the PDF's text layer): "let N_q(α, T) be the total number of zeros s = σ + it for all L-functions modulo q that occur in the rectangle α < σ < 1, |t| ≤ T. In order to state a general result suitable for further advances, we assume that for some constant b > 1 the uniform bound N_q(α, T) ≪ (qT)^{b(1−α)} ℓ^{O(1)} (3.3) holds … By a result of Huxley [6] we can take b = 12/5 in (3.3); see also [8, Equation (18.13)]". Their [8] is Iwaniec–Kowalski, *Analytic Number Theory*, which was not read here.
- **(H2) at `7/3`.** B. Chen, V. Gupta and Y. C. Li, arXiv:2507.08296. Its abstract states `Σ_{χ mod q} N(σ, T, χ) ≪_ε (qT)^{7(1−σ)/3+ε}` and "The exponent 7/3 improves upon Huxley's earlier exponent of 12/5". Not checked here. A factor `(qT)^ε` in place of `(log qT)^B` suffices for the theorem: in 3.9 it costs `q^{2ε}`, which is absorbed once `2ε < η(1 − θ₀)/4`.
- **Classical tools.** Mellin inversion; Cauchy's theorem on rectangles; the Borel–Carathéodory inequality (Titchmarsh, *The Theory of Functions*, §5.5); partial summation; the Euler product on `Re s = 2`; `θ(y) ≤ 2y`; and the error term from (H1) for `ζ` (in this stack, round 467's `HalfPlanePNT.psi_isBigO_eleven_twelfths` for `ψ`).

## 6. Literature searched (2026-10-16)

- **Linnik's constant.** Wikipedia's "Linnik's theorem" lists Xylouris `5` (2011), `5 − ε` (2018) and "2026, Naslund (work done with AI): L ≤ 3.99". Under GRH it gives `p(a, d) ≤ φ(d)²(log d)²` (Lamzouri, Li and Soundararajan).
- **Naslund's 3.99** (github.com/enaslund/linniks-constant-3.99; registered 2026-10-01). The repository's README states "every reduced residue class modulo `q` contains a prime below `q^3.99`" for "every sufficiently large modulus `q`". Its hypotheses are lemmas of Xylouris (2011), Heath-Brown (1992) and Graham (1978). It does not mention a zero-free half-plane. Its method is the classical one.
- **Bruna** (arXiv:2603.25612, March 2026). Under the generalized Lindelöf hypothesis, `p ≪ q^{2+ε}`. The search summary says the proof uses a zero-free region, log-free density estimates and zero repulsion; that summary is not the paper's text.
- **Frei, Sofos and Widmer** (arXiv:2610.18491, 13 October 2026). An effective Chebotarev theorem under "no zeros with `ℜ(s) > 1 − δ`" for `ζ_L`. Its least split prime has norm about `(log Δ_L)^{1/δ}` up to `log log` factors. Per the fetched text, its body states no zero-density estimate and does not mention arithmetic progressions.
- **The release's preprints** (`/home/user/openai/math/preprints`, 722 directories). A grep for "Linnik" hits 11 preprints. In the matches read, they cite Linnik's theorem or papers. "Uniform exclusion of Landau–Siegel zeros" (October 1, 2026) proves `(1 − β) log q ≥ c` for real zeros; it states no Linnik constant.
- **Not read:** Huxley (1974/75); Iwaniec–Kowalski chapter 18 around (18.13); Heath-Brown (1992); the full texts of Cureton–Thorner, Liu, Kintali, Sang and Xu–Sang.

No source read states the deduction "(H1) and (H2) give `L ≤ A + η`". It is a short combination of standard tools. The closest statements found are Bruna's (generalized Lindelöf gives `2 + ε`) and Frei–Sofos–Widmer's (a zero-free half-plane gives a small split prime, without a density estimate). Novelty is unconfirmed: the search covered the sources listed only.

## 7. Toward Lean

README round 519's plan. The proof of section 3 avoids the explicit formula over zeros. Per character it needs only Mellin inversion, Cauchy's theorem on rectangles, a log-derivative bound in a zero-free disc, and the count of characters with a zero to the right of `σ`. So the deduction "(H1) and (H2) give `L ≤ A + η`" can be machine-checked with (H2) as a displayed hypothesis before any density estimate is formalized.

## 8. How this was checked

- The lead's derivation (sections 1–3), written step by step with the constants.
- `params.py` (section 4): 20 cases, 0 failures.
- An independent review in a fresh context: see README round 519 for its findings and their dispositions.
