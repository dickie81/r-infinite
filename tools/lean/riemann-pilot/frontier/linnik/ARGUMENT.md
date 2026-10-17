# Linnik's constant from a zero-free half-plane and a zero-density estimate

README round 519. This is a paper argument. Nothing in it is machine-checked, and it has not been refereed. Section 8 records how it was checked.

## 1. Statement

**Notation.** For `q ≥ 1`, `X(q)` is the set of Dirichlet characters mod `q`, and `χ₀` is the principal one. For `χ ∈ X(q)`, `Z(χ)` is the multiset of zeros `ρ = β + iγ` of `L(s, χ)` with `0 < β < 1`. For an imprimitive `χ`, `L(s, χ)` is the primitive `L(s, χ*)` times finitely many Euler factors `1 − χ*(p)p^{−s}`, whose zeros lie on `Re s = 0`, so `Z(χ) = Z(χ*)`. For `1/2 ≤ σ ≤ 1` and `T ≥ 2`,

```
N(σ, T; q) = Σ_{χ ∈ X(q)} #{ρ ∈ Z(χ) : β ≥ σ, |γ| ≤ T}.
```

**Hypotheses.**

- **(H1) at `θ₀`, a zero-free half-plane.** For every `q ≥ 1`, every `χ ∈ X(q)` and every `s` with `Re s > θ₀`, `L(s, χ) ≠ 0`; for `χ = χ₀`, `s ≠ 1`. (H1) at `θ₀` gives (H1) at `max(θ₀, 1/2)`, so below `θ₀ ≥ 1/2`.
- **(H2) at `(A, B)`, a zero-density estimate over the characters of one modulus.** There is `C ≥ 1` such that `N(σ, T; q) ≤ C (qT)^{A(1−σ)} (log qT)^B` for every `q ≥ 1`, `T ≥ 2` and `1/2 ≤ σ ≤ 1`.

**Theorem.** Assume (H1) at some `θ₀ < 1` and (H2) at some `(A, B)` with `A ≥ 2`. For every `η ∈ (0, 1]` there is `q₀` such that, for every `q ≥ q₀` and every `a` prime to `q`, there is a prime `p ≡ a (mod q)` with `q^{A+η} ≤ p ≤ 2q^{A+η}`. So the least such prime satisfies `p(q, a) ≪_η q^{A+η}` for every `q`. The implied constant is effective when the constants of (H2) are; (H1) enters only as a statement that zeros are absent.

**Instances.**

| (H1) | (H2) | exponent `L` | status of the inputs |
|---|---|---|---|
| `θ₀ = 11/12`: `Eis.LFunction_ne_zero_of_re_gt` | `A = 12/5`: Huxley (1974/75) | `12/5 + η` | (H1) kernel-checked in this stack; (H2) published |
| `θ₀ = 11/12` | `A = 7/3`: Chen–Gupta–Li (2025) | `7/3 + η` | (H2) a preprint, not checked here; their own Corollary 1.4 already gives this row (section 6) |
| `θ₀ = 11/12` | `A = 1 + 2θ₀ = 17/6`: round 518's route over the characters mod `q` | `17/6 + η` | (H2) not proved; section 7 and README round 519 |
| `θ₀ = 7/8`: the release | `A = 12/5` | `12/5 + η` | (H1) the release's claim, not checked here |

For comparison: Xylouris proved `L = 5` (2011) and `5 − ε` (2018); Naslund claims `3.99` (2026, a preprint); the generalized Riemann hypothesis gives `2 + η`. Section 6 has the sources.

**Without (H2).** The proof below with the trivial count `Σ_χ x^{σ_χ} ≤ φ(q)x^{θ₀}` in place of 3.9 gives `L = 1/(1 − θ₀) + η`: `12 + η` at `θ₀ = 11/12`, which is STRUCTURAL-REVIEW's K2.

## 2. Why it works

The zeros with real part about `σ` contribute about `(q^A/x)^{1−σ}` to the count of primes up to `x` in a class mod `q`, where `A` is the density exponent. Classically there can be zeros with `1 − σ` as small as `c/log q`. At `x = q^L` such a zero contributes `exp(−c(L − A))`, a constant rather than a small quantity. The record proofs (Heath-Brown 1992, Xylouris 2011; not read here, [recalled]) control these zeros with the zero-free region, log-free density estimates and the Deuring–Heilbronn phenomenon, and reach exponents of about `5`; sieve proofs reach much larger exponents (section 6). Under (H1), `1 − σ ≥ 1 − θ₀` for every zero, so every contribution is at most `q^{−(L−A)(1−θ₀)}`, and any `L > A` works.

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

**3.3 The principal character.** `S_{χ₀}(x) = Σ_n Λ(n)w(n/x) − Σ_{p | q} Σ_{m ≥ 1} log p · w(p^m/x)`. For each `p` at most two `m` have `x ≤ p^m ≤ 2x`, so the second sum is at most `2 log q`. (H1) for `ζ` (the case `q = 1`) gives `ψ(u) = u + O(u^{θ₀+δ})`: at `θ₀ = 11/12` this is round 467's `HalfPlanePNT.psi_isBigO_eleven_twelfths`, and for general `θ₀` it is the classical consequence of a zero-free half-plane and a polynomial bound for `(s − 1)ζ(s)` on `1/2 ≤ Re s ≤ 3` [recalled]; the bound (∗) below uses `|Σ_{n≤u} χ(n)| ≤ q` and does not apply to `ζ`. Partial summation against `w` gives `Σ_n Λ(n)w(n/x) = −∫ ψ(u)w′(u/x) du/x = x ŵ(1) + O(x^{θ₀+δ})`. So `S_{χ₀}(x) ≥ x ŵ(1) − c x^{θ₀+δ} − 2 log q`. (A lower bound `S_{χ₀}(x) ≥ c₀x` with any fixed `c₀ > 0` would do, since 3.10 shows the other characters contribute `o(x)`; the Lean route uses `e^{−n/x}` in place of `w` and Chebyshev's `ψ(x) ≥ x/4`.)

**3.4 A zero-free region for each character.** For `χ ≠ χ₀` let

```
σ_χ = max({1/2} ∪ {β : ρ ∈ Z(χ), |γ| ≤ 2T}),
```

a maximum over a finite set. By (H1), `σ_χ ≤ θ₀`. `L(s, χ)` is entire with no zero in `D_χ = {Re s > σ_χ, |Im s| < 2T} ∪ {Re s > θ₀}`. Its zeros with `0 < Re s < 1` and `|Im s| < 2T` have `Re s ≤ σ_χ`, it has no zero on `Re s ≥ 1`, and its other zeros have `Re s ≤ 0`.

**3.5 The log-derivative in `D_χ`.** Let `χ ≠ χ₀`. For `s` with either (a) `σ_χ + δ ≤ Re s ≤ 2` and `|Im s| ≤ T`, or (b) `θ₀ + δ ≤ Re s ≤ 2`:

```
|F_χ(s)| ≤ (48/δ²) log(10q(|Im s| + 5)).     (∗)
```

*Proof.* Put `s₁ = 2 + i Im s` and `r = |s − s₁| = 2 − Re s`. Put `R = 2 − σ_χ − δ/2` in case (a) and `R = 2 − θ₀ − δ/2` in case (b), so that `R − r ≥ δ/2` and `R ≤ 3/2`. The last uses `σ_χ ≥ 1/2` in case (a) and `θ₀ ≥ 1/2` in case (b) (section 1).

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

`params.py` checks, in exact rationals, the exponent inequalities that 3.1, 3.10 and 3.11 use, in the forms the text uses, for the five instances `(A, θ₀) = (12/5, 11/12), (7/3, 11/12), (17/6, 11/12), (12/5, 7/8), (11/4, 7/8)` and `η = 1, 1/10, 1/100, 1/1000`. All 20 cases pass. Each inequality follows from the formulas of 3.1 for every `A ≥ 2`, `1/2 ≤ θ₀ < 1` and `0 < η ≤ 1`, so the census checks that the formulas were transcribed into the inequalities correctly, not independent facts. To show that the checks can fail, the script also runs three mis-transcribed parameter choices (`δ₁ = η/A`, `δ` twice as large, `k = ⌈1 + 2A/η⌉`) and an instance with `A < 2`, and requires each to fail at least one case. It checks arithmetic only, not the analysis.

## 5. Inputs and sources

- **(H1) at `11/12`.** `Eis.LFunction_ne_zero_of_re_gt` (`src/DirichletCharHalfPlane.lean:207`, rounds 492–495). Its docstring reads: "for every modulus `q ≥ 1`, every Dirichlet character `χ` mod `q` and every `s` with `Re s > 11/12`, `L(s, χ) ≠ 0`, the trivial character excepted at `s = 1`. The real characters are round 477's." Its axioms are `propext`, `Classical.choice` and `Quot.sound`. It is only as strong as the faithfulness of its statement (round 466's note on `riemannZeta` and `DirichletCharacter.LFunction` applies).
- **(H2) at `12/5`.** M. N. Huxley, "Large values of Dirichlet polynomials. III", Acta Arith. 26 (1974/75), 435–444, which was not read here. It is read as quoted by Banks and Shparlinski (arXiv:1605.07553v2, section 3; symbols decoded from the PDF's text layer): "let N_q(α, T) be the total number of zeros s = σ + it for all L-functions modulo q that occur in the rectangle α < σ < 1, |t| ≤ T. In order to state a general result suitable for further advances, we assume that for some constant b > 1 the uniform bound N_q(α, T) ≪ (qT)^{b(1−α)} ℓ^{O(1)} (3.3) holds … By a result of Huxley [6] we can take b = 12/5 in (3.3); see also [8, Equation (18.13)]". Their [8] is Iwaniec–Kowalski, *Analytic Number Theory*, which was not read here.
- **(H2) at `7/3`.** B. Chen, V. Gupta and Y. C. Li, arXiv:2507.08296. Its abstract states `Σ_{χ mod q} N(σ, T, χ) ≪_ε (qT)^{7(1−σ)/3+ε}` and "The exponent 7/3 improves upon Huxley's earlier exponent of 12/5". Not checked here. A factor `(qT)^ε` in place of `(log qT)^B` suffices for the theorem: in 3.9 it costs `q^{2ε}`, which is absorbed once `2ε < η(1 − θ₀)/4`. Their Corollary 1.4 already draws this row's consequence from a zero-free hypothesis that (H1) implies (section 6).
- **Classical tools.** Mellin inversion; Cauchy's theorem on rectangles; the Borel–Carathéodory inequality (Titchmarsh, *The Theory of Functions*, §5.5); partial summation; the Euler product on `Re s = 2`; `θ(y) ≤ 2y`; and the error term from (H1) for `ζ` (in this stack, round 467's `HalfPlanePNT.psi_isBigO_eleven_twelfths` for `ψ`).

## 6. Literature searched (2026-10-16, extended 2026-10-17 after the review)

- **Linnik's constant.** Wikipedia's "Linnik's theorem" (raw wikitext, fetched 2026-10-17) tabulates `L ≤` values: Xylouris `5` (2011) and `5 − ε` (2018), and a 2026 row `3.99`, Naslund, marked "(work done with AI)". Under GRH it gives `p(a, d) ≤ φ(d)²(log d)²` (Lamzouri, Li and Soundararajan).
- **Naslund's 3.99** (github.com/enaslund/linniks-constant-3.99). Its README: "The paper proves that for every sufficiently large modulus `q`, every reduced residue class modulo `q` contains a prime below `q^3.99`. That bound is **not** formally verified here." The registration of 2026-10-01 "covers the formalized components described below, not the bound `L ≤ 3.99` itself", and "This does not prove Linnik's constant 3.99." The formalized analytic part "is **conditional** on printed results, each stated as a hypothesis no stronger than its source, and on one derived statement": results of Xylouris (2011), Heath-Brown (1992) and Graham (1978), and `OrdinaryEnvelope` "(derived, not printed)". It does not mention a zero-free half-plane. Its method is the classical one.
- **Bruna** (arXiv:2603.25612v1, 26 March 2026). Theorem 1.1: under the generalized Lindelöf hypothesis (GLH), `P(a, q) ≤ q^{2+ε}` for `q ≥ q(ε)`. Its text: "The proof follows a classical strategy using three key principles of Dirichlet L-functions: A zero-free region, log-free zero-density estimates, and a zero-repulsion theorem. Under GLH, we obtain an arbitrarily large zero-free region and the density hypothesis in the entire half-strip." It also records sieve proofs: "Friedlander and Iwaniec [FI23a, FI23b] used classical sieve methods to prove Linnik's theorem with L = 75 744 000, whereas Matomäki, Merikoski, and Teräväinen [MMT] developed a new prime-detecting sieve that gave the much stronger bound P(a,q) ≪ q^350."
- **Chen, Gupta and Li** (arXiv:2507.08296v2). Corollary 1.4 ("Primes in arithmetic progressions under a good zero-free region"), read from the PDF's text layer: "Suppose that ∏_{χ mod q} L(s,χ) ≠ 0 for σ ≥ 1 − η(q,T) when |Im(s)| ≤ T and that η(q, x^{ϵ/3}T₀) log x → ∞ as x → ∞ uniformly for q < h/x^{17/30−ϵ}, where T₀ = (x/h)^{1+o(1)}. Then ψ(x+h;q,a) − ψ(x;q,a) = (1 + o_{η,ϵ}(1)) h/ϕ(q), (1.6) provided that … For all h and q, we have (1.6) provided that h/ϕ(q) ≥ x^{1/2+ϵ}q^{1/6} + x^{17/30+ϵ}. This can be deduced from Theorem 1.2 via a smoothed version of the explicit formula." (H1) gives their hypothesis with `η(q, T) = (1 − θ₀)/2`. At `h = x` the proviso holds once `x ≥ q^{7/3+O(ϵ)}` (the second term needs only `30/13 < 7/3`), and `q < x^{13/30+ϵ}` holds there. So (H1) at `11/12` with their Corollary 1.4 gives `L ≤ 7/3 + ε`: the table's second row, with Chen–Gupta–Li's own deduction in place of section 3.
- **Banks and Shparlinski** (arXiv:1605.07553v2; published as "Bounds on short character sums and L-functions with characters to a powerful modulus", J. Anal. Math. 139 (2019) 239–263, per the Springer page, whose abstract says the paper improves "the previous best value L = 12/5 = 2.2 of the Linnik constant for primes in arithmetic progressions modulo powers of a fixed prime to L < 2.1115"; the sic is theirs, `12/5 = 2.4`). Their Theorem 3.5 of the arXiv version is the same deduction for the moduli `q = p^γ` (`p` a fixed odd prime), with their own zero-free region for those moduli: "Suppose (3.3) holds with some constant b > 1. … For any modulus q = p^γ with γ ∈ N, any integer a coprime to p, and any positive real numbers x and h for which q x^{1−1/b+ε} ≤ h ≤ x ≤ q^{1/ε}, we have ψ(x+h; q,a) − ψ(x; q,a) = h/ϕ(q) + O_ε(h exp(−c₀(log x)^{1/3}(log log x)^{−1/3}))". At `h = x` this is `L = b + ε` for those moduli. Its proof "closely follows that of Gallagher [4, Theorem 2]", and its section 6.4 bounds `∫ x^{α−1}N_q(α, T) log x dα`, the integral of 3.9.
- **Frei, Sofos and Widmer** (arXiv:2610.18491, 13 October 2026). An effective Chebotarev theorem under "no zeros with `ℜ(s) > 1 − δ`" for `ζ_L` (their QRH(δ)). Their Corollary 1.2 gives split primes of norm `x ≥ c(δ)(log Δ_L)^{1/δ}(log log Δ_L)^{2/δ}`, with no zero-density estimate. They cite Pollack, who "observed that Linnik's theorem gives p ≪ Δ_L^{2C/[L:Q]}, where C denotes Linnik's constant". At `L = ℚ(ζ_q)` their Corollary 1.2 is the "Without (H2)" bound of section 1, `1/δ` up to `log` factors.
- **The release's preprints** (`/home/user/openai/math/preprints`, 722 directories). A case-sensitive `grep -rl "Linnik"` hits 9 of them; a case-insensitive grep hits 11, the two extra being "Malinnikova" in two papers on nodal sets. In the matches read, they cite Linnik's theorem or papers. "Uniform exclusion of Landau–Siegel zeros" (October 1, 2026) proves `(1 − β) log q ≥ c` for real zeros; it states no Linnik constant.
- **Not read:** Huxley (1974/75); Iwaniec–Kowalski chapter 18 around (18.13); Gallagher (1970); Heath-Brown (1992); the full texts of Cureton–Thorner, Liu, Kintali, Sang and Xu–Sang.

**The deduction is in the literature.** Chen–Gupta–Li's Corollary 1.4 (all `q`, their density estimate, a zero-free hypothesis that (H1) implies) and Banks–Shparlinski's Theorem 3.5 (prime-power moduli, any density exponent `b`) are this deduction, by Gallagher's method through the explicit formula; Bruna's Theorem 1.1 is its case `A = 2` under GLH, which supplies the density hypothesis and a zero-free region but no half-plane, so a zero-repulsion theorem handles the exceptional zero. Section 3 differs only in moving each character's line to its own zero-free region instead of summing over zeros. So the combination "(H1) and (H2) give `L ≤ A + η`" is not new. With the stack's half-plane, Chen–Gupta–Li's Corollary 1.4 already gives `7/3 + ε`, better than this note's `17/6 + η` row. What the stack can add is a kernel-checked proof: the `17/6 + η` row needs no input from outside the stack (section 7), while the `7/3` and `12/5` rows need a density estimate that is not formalized here.

## 7. Toward Lean

The proof of section 3 avoids the explicit formula over zeros. Per character it needs only Mellin inversion, Cauchy's theorem on rectangles, a log-derivative bound in a zero-free disc, and the count of characters with a zero to the right of `σ`. So the deduction "(H1) and (H2) give `L ≤ A + η`" can be machine-checked with (H2) as a displayed hypothesis (Phase A). The `17/6` row then needs (H2) at `A = 2 + 4c` from a bound `|L(1/2 + it, χ)| ≪ (q(|t| + 2))^c` (Phase B: round 518's detection and large-values route, run over the characters mod `q` with one zero per character) and that bound at `c = 5/24 + ε` from (H1) (Phase C: round 517's interpolation, uniform in `q`, with the functional equation of `L(s, χ)`). `1 + 2θ₀ = 2 + 4c` at `c = (2θ₀ − 1)/4`. The Lean route changes three things in section 3: the weight is `e^{−n/x}`, whose Mellin transform `Γ(s)` decays exponentially, so `T` is `O(log q)` rather than `q^{δ₁}`; the principal character needs only Chebyshev's `ψ(x) ≥ x/4`, since `Σ_n Λ(n)e^{−n/x} ≥ ψ(x)/e`; and `σ_χ` runs over a finite grid of levels, so that (H2) is applied at finitely many `σ`. README round 519 records the plan step by step. *(Round 520: Phase A is kernel-checked, `Linnik.linnik_of_charDensity` in `external/pnt/LinnikDeduction.lean`. Its hypothesis `CharDensity A B C` counts the characters with a zero rather than the zeros, so (H2) implies it; it holds for every `q ≥ 1` and gives a prime `p ≤ K q^{A+η}` rather than one in `[q^{A+η}, 2q^{A+η}]`. The half-plane alone gives `CharDensity 12 0 1`, hence the exponent `12 + η` (`linnik_twelve`). Phases B and C are not started. README round 520.)*

## 8. How this was checked

- The lead's derivation (sections 1–3), written step by step with the constants.
- `params.py` (section 4): 20 cases, 0 failures; each of its four mutations fails at least one case.
- An independent review in a fresh context (2026-10-17): no MAJOR findings, 7 minor and 8 cosmetic, all verified by the lead against the sources and fixed here. The two that matter most: Chen–Gupta–Li's Corollary 1.4 and Banks–Shparlinski's Theorem 3.5 state the deduction (section 6), so the earlier "No source read states the deduction" was false and is withdrawn; and `params.py`'s checks could not fail on any admissible input (section 4). README round 519 lists all fifteen findings and their dispositions.
