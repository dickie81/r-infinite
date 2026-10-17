# Layer II: exponential-sum bound from VMVT, paper proof to formalise (round 203)

Route after T. Tao, 254A Notes 5 (2015), Theorem 2(ii). For each fixed `n` the bilinear double
sum is bounded directly; no spacing lemma over `n` is needed.
`e(θ) = exp(2πiθ)`; `‖θ‖` is the distance from `θ` to the nearest integer.

**(A) Geometric sum.** `|Σ_{y=u+1}^{u+Y} e(θy)| ≤ min(Y, 1/(2‖θ‖))`.

**(B) One-dimensional bilinear bound.** For `X, Y ≥ 1` and `0 < |α| ≤ 1/2`,
`Σ_{|z|≤X} min(Y, 1/(2‖αz‖)) ≤ (4X|α| + 2)·(2Y + (2/|α|)(1 + log(1/|α|)))`.
Split `z` into blocks of length `⌊1/(2|α|)⌋`; in each block `αz mod 1` meets each integer's
neighbourhood at most once.

**(D) Double Hölder (the link to VMVT).** For `α ∈ ℝ^K`, `M, ℓ ≥ 1`, let
`Σ(α) = Σ_{a,b=1}^{M} e(Σ_{j=1}^{K} α_j a^j b^j)`. Then
`|Σ(α)|^{2ℓ²} ≤ M^{4ℓ(ℓ−1)} · J_{ℓ,K}(M)² · Z(α)`, where
`Z(α) = max_{x ∈ X} Σ_{x' ∈ X} |Σ_{y ∈ X} e(α·(x − x')·y)|` and
`X = {pv(b) : b ∈ [1,M]^ℓ} ⊆ ∏_j [ℓ, ℓM^j]`.

Proof:
1. power mean in `a`;
2. `(Σ_b e(α·A(a)A(b)))^ℓ = Σ_y ν(y) e(α·A(a)y)`, with `ν` the representation count;
3. weighted power mean plus Cauchy–Schwarz give
   `(Σ_y ν|F|)^{2ℓ} ≤ (Σν)^{2ℓ−2}·(Σν²)·Σ_y|F|^{2ℓ}`;
4. `Σ_y |F|^{2ℓ} ≤ J·Z`, by expanding `|F^ℓ|²` and using `ν(x)ν(x') ≤ (ν(x)² + ν(x')²)/2`.

Here `Σν = M^ℓ` and `Σν² = J_{ℓ,K}(M)`. The inner sum over the box factorises by coordinate,
and each factor is bounded by (A) and then (B).

**(E) Shift and Taylor.** For `f(x) = −(t/2π) log x`, `N < n ≤ 2N`, and `1 ≤ a, b ≤ M` with
`M² ≤ N/2`:
`f(n + ab) = f(n) + Σ_{j=1}^{K} α_j(n)(ab)^j + ρ`, with `α_j(n) = (−1)^j t/(2π j n^j)` and
`|ρ| ≤ (t/2π)(2M²/N)^{K+1}`. Also `Σ_{N<n≤2N} e(f(n)) = M^{−2} Σ_{a,b} Σ_n e(f(n+ab)) + O(M²)`.

**(F) Assembly.** Choose `M ≈ N^{1/4}` and `K ≈ 3 log t / log N`. For `j` in a range of order `K`,
`|α_j(n)|` lies in the good window `[M^{−(2−c)j}, M^{−cj}]`, where (B) saves `M^{−cj}`. Combined
with explicit VMVT (`J_{ℓ,K}(M) ≤ C M^{2ℓ − K(K+1)/2 + η}`) this gives
`|S| ≤ N^{1 − θ(K)}`.

**(G) ζ growth.** Partial summation over dyadic blocks gives `PolylogGrowth a K` for some
`a < 1`. The exponent `a` depends on `θ(K)`, and hence on the weak VMVT's `s ≈ k³`.
