# The release's exponent system at 5/6

Side-branch note, 2026-10-22, on branch `claude/latest-commit-branch-ik1pj3`. It follows `PAIRING.md` in this directory. It is not a README round, and it adds no Lean. The numbers below come from the gate script `fivesixths.py` (section 6), or are quoted from the sources cited.

**The question.** The owner's goal: "widen the zero free strip to at least 5/6", that is, a zero-free half-plane `Re s > 5/6` for the release's families. This note asks what the release's method, as the pilot models it (README rounds 496–508, `frontier/wall78`), would need to reach `5/6`. It does not reach it. It finds where `5/6` sits in that exponent system and names the two inputs that are missing.

**Summary.**
1. **Horizon scan** (section 0). Nothing found reaches `5/6`. The best recorded boundary is Liu's `B_♭ = 0.874886647…` (arXiv 2610.26835, 19 October, every number field).
2. **5/6 is the floor of the release's low side** (gate F1, exact). Given the Gram bound's range `b ≥ 0` and the compensated probe's `l_x > ℓ`, the low side satisfies `s₀ − 5/6 = (M − 2ℓ)/12 + (Gram excess) + L/2 + μ/2 ≥ (l_x − ℓ)/6 ≥ 0` in every geometry. Equality holds only at `l_x = l_y = ℓ` with no row loss and no crossing *(at round 500's crossing cost `c = 1`; at a smaller cost a crossing is cheaper, and at `c = 0` free: section 8)*. In `PAIRING.md`'s reading, `β_b = 5/6 − ℓ/6 + M/12 + L/2`. There the amplifier's gain `ℓ/6` is exactly what the theta deficit `M/12` takes back once `M ≥ 2ℓ`.
3. **The second branch is a slot sum at a trivial dual** (gates F3, N1).
   - Round 500's second branch is attained at a dyad whose dual is trivial and whose slots are all active. There the completed row is a fixed multiple of `Σ_P a(P)/√q_P`, and Lemma `lem:hybrid-energy` bounds that sum by Cauchy–Schwarz.
   - By the release's marked reflection, `a(P)` is a product, over the active slot primes `q`, of the normalized cubic Gauss sum `γ₂(q)`, the angle `ᾱ(q)²` and finite-order characters.
   - Over the ~~7827~~ 7796 split primes of norm `≤ 8·10⁴` *(section 14: the 7827 included 31 inert primes; the values are now over split primes only)*, of the twists `α^k` with `|k| ≤ 3` only the untwisted sum `Σ γ₂(π)` carries Patterson's main term: ~~`893`~~ `862` against `√n = 88`. Every twist `α^k` with `k ≠ 0` is at square-root size; at `k = −2`, the slot coefficient's twist, the sum is ~~`91`~~ `122`.
4. **The low side's least value** (gate F2, closed form). ~~Let `σ` be the slot sum's exponent: its square is `Z^{σ z_a}`.~~ *(Struck in section 7: `σ` is the parameter of the second branch `(1 + (4σ − 1)ℓ′ − 2M′)/4`, not the exponent of a slot sum at the trivial dual.)* Then the least low side over all geometries is `5/6 + max(0, (2σ − 1)/(6(4σ + 1)))`:
   - `13/15` at the release's `σ = 1`;
   - `28/33` at `σ = 2/3`, ~~the size of the cubic large sieve's `(NL)^{2/3}` term at a trivial dual~~ *(section 7: the hybrid bound with the `L` term dropped at every dual length)*;
   - exactly `5/6` for every `σ ≤ 1/2`.
5. **The whole exponent system at 5/6** (gates F4, F5, F6). Take round 499's program with round 500's crossing cost, Xu–Sang's admissibility rows and round 498's readings. Add four more:
   - no numerator rotation, which makes Xu–Sang's `h < 2l_y` idle;
   - the third Gram term carried in the low side's maximum;
   - the small rows' `z`-line near `1/6`;
   - a uniform row-sum saving `U^η` on every bin.

   With all of these, the boundary is `5/6`, at the vertex `l_x = l_y = ℓ = 1/3`, provided `σ ≤ 1/2` and `η ≥ 0.168`; Xu–Sang's own counts and fourth moment need `η ≥ 0.178`. At `σ = 2/3` the same system gives `28/33`.
6. **What is missing.** Two estimates, neither in the sources read here *(section 8: with round 500's crossing cost; a cheaper crossing of the slice is a third route)*:
   - ~~the release's trivial-dual slot sums with `σ ≤ 1/2`, that is, angle-twisted cubic Gauss sums over primes below `X^{3/4}`;~~ *(struck in section 7: such sums, at square-root size in every column, give only `σ = 5/8` and `71/84`; `σ ≤ 1/2` needs a square-root cubic large sieve `N + (NL)^{1/2}` for the slot coefficients;)* *(Section 9: "at square-root size" is wrong there. The `5/8` row is squared slot sums `≪ L^{1/2}` in every column, that is slot sums `≪ L^{1/4}` (before the `1/√q_P` normalization, `≪ L^{3/4}`); square-root cancellation in every column gives `5/6`. And `σ = 1/2` also follows from the weaker `N + N^{3/4}L^{1/2}`.)*
   - a saving `U^{1/6}` on the high side's sums over the Poisson rows near `a = 1/2`, where the C₀ wall sits.

   The register gets both as targets (section 5). This note does not prove either, and so does not prove `Re s > 5/6`.
7. **Follow-up (section 7, gate script `slotsplit.py`).**
   - The literature: Heath-Brown's twisted bound `X^{5/6+ε} + |l|X^{3/4+ε}`, and Dunn–Radziwiłł's proof, under GRH, that the cubic large sieve's `(AB)^{2/3}` term is sharp.
   - A slot-split bound from the release's own pair phase: `σ = 3/4`, least low side `41/48` (S1, S2). *(Superseded the same day: the trilinear split gives `σ = 2/3`, least low side `28/33`; section 9.1, gate S8.)*
   - The dictionary between hybrid bounds and `σ`, which corrects items 4 and 6 (S5). *(Its labels are corrected in section 9.5.)*
   - With the release's inputs and no row saving, the boundary stays `0.8748866` at every `σ` (S3).
   - At the vertex, every bin with `δ < 1/2` needs a saving beyond what density-hypothesis counts give (S4).
   - The goal is still not reached.
8. **The crossing cost (section 8, gate S6).**
   - Round 500's first branch charges a crossing of the slice `M + ℓ = 1` at cost `c = 1`.
   - In the model, with the slot-split's `σ = 3/4` and no row saving, `c = 0.15`, `0.1` and `0.05` give `0.8725510`, `0.8615362` and `0.8486654`. *(The same at the trilinear `σ = 2/3`: S6, section 9.)*
   - ~~`c = 0` gives `5/6` on the ray `l_x = l_y = ℓ ≥ 1/2`, with neither T1 nor T2.~~ *(False as written: on the ray `l_x = l_y = ℓ = t` the bins `E` bind below a threshold `t* ∈ (0.557239, 0.557240)`, and at `t = 1/2` the boundary is `0.8786610`. `c = 0` gives `5/6` on the ray for `t ≥ t*`, still with neither T1 nor T2: S6, sections 9 and 9.7.)*
   - These geometries lie far across the slice, where the release's lemmas were not re-derived.
9. **The trilinear split and the review of sections 7–8 (section 9, gate S8).**
   - A hostile review found that the trilinear split's character is `conj((B/jA)_3)`, with a squarefree modulus. Heath-Brown's sieve then gives `N + (NL)^{2/3}`: `σ = 2/3`, least low side `28/33`, by a written argument checked against the release's lines (9.1). Alone it moves nothing: the boundary stays `0.8748866` (S3).
   - The slot coefficient is the composite cubic Gauss sum `γ₂(P)`, angle-twisted: the release's one-prime scalar `τ⁺_{q,2}` and its pair phases combine by the Chinese remainder theorem (9.2, S8).
   - ~~Dunn and Radziwiłł's corrected sieve assumes, for prime-supported coefficients, input of GRH strength: circular here (9.2).~~ *(Misdescribed, the second review round, 9.7. For the slot coefficients Dunn and Radziwiłł's axiom (3.2) either fails outright or asks for a zero-free region `Re s > 1/2 + η`, with `η ≤ 1/4`, for a fixed `L`-function of the release's family. That is not GRH, but it is more than the `5/6` sought, so either way the route is unusable as stated: 9.2.)*
   - The review's other findings are swept (9.4). The goal is still not reached.
   - A second, convergence round of the review returned no major finding, four minor and eight cosmetic ones, all swept (9.7).
10. **A horizon hit (section 10).** OpenAI's "An unconditional first moment for cubic Gauss sums" (September 25), cited but not used by the release, proves Patterson's first moment and its fixed angular twists without GRH. For the slot coefficients it bears on the trivial dual, which does not move `σ`. Its power-saving Proposition `prop:dual` for prime convolutions is recorded as a T1 attack note. *(9.7: it bears on T1 more directly. Its Proposition `prop:dispersion` has T1's shape, for `L ≤ N ≤ L^{2.125}`, and saves only a power of `log X` after its theta correction; section 10.)*
11. **The high side's first rung (section 11, gates H1–H6 of `highside.py`; H7 added in section 13).** In the release-level configuration the binding bins lie at `x = 1/2`, `δ ≈ 0.47`. A uniform saving `U^η` on the bins `δ ≥ 1/8` moves the boundary by about `0.185η`, down to `0.8667866` at `η = 0.045`, where the floor bin binds. Density-hypothesis counts there, a `2k`-th moment with `k = 6`, or Lemma 17.6's slope lowered to `1/8` reach the same value. ~~From there `13/15` is a step of `1.2·10⁻⁴`, and at `13/15` the rotation's condition binds (round 498).~~ *(Struck in section 13, false as written at `σ = 2/3`: savings on every bin, the floor bin included, continue below `13/15` with Sang's rotation kept, down to `41/48`, the rotation's own floor. `13/15` stops only a saving confined to the floor and small bins, and the release's `σ = 1`.)* *(Section 14: `41/48` is that floor under the program's soft third; with Xu–Sang's `l_y − ℓ > 11b/6` kept it is `253/294`.)* ~~T3's pointwise route has effective crossing cost `0.83`, against a break-even below `0.165`.~~ *(Struck in section 13: the ratio `0.83` belongs to one dyad, and is `1/7` at another. T3's pointwise route charges the low side at least `min(μ, ℓ)/2`, and the program charging `ℓ/2` gives `0.9487180`, so the route leaves the boundary at `0.8748866`.)* The goal is still not reached.
12. **Horizon refresh (section 12).** Nothing new reaches `5/6`. A Lindelöf-on-average lemma for the cubic Kubota series (David, de Faveri, Dunn and Stucky) ~~would give T1 for smooth slots~~ *(section 13: gives `σ = 2/3` for smooth untwisted slots, and T1 for smooth angle-twisted slots only if the pole at `4/3` vanishes under the twist and the lemma extends to it, neither checked here)*; on that reading the obstruction is the prime support of the release's slots.
13. **The third review round (section 13).** One major finding: at `σ = 2/3`, `13/15` is not an obstruction after the first rung. With savings on every bin and density-hypothesis counts, the boundary goes to `41/48` with Sang's rotation kept, which is that rotation's exact floor, and to `28/33` without it. *(Section 14: `41/48` is that floor under the program's soft third, round 499's reading that drops Xu–Sang's `l_y − ℓ > 11b/6`; with that condition kept the floor is `253/294`.)* Five minor findings and seven cosmetic ones are also swept. Two gates are added: H7, on where density-hypothesis counts would have to hold, and N6, on two-prime slots. The goal is still not reached.
14. **The fourth review round and the T1–T3 trade-off (section 14, gate H8).**
    - The review found no major defect; its three minor and eight cosmetic findings are swept. The rotation's floor `41/48` holds under the program's soft third; with Xu–Sang's `l_y − ℓ > 11b/6` kept it is `253/294` (H4 (iv)). N1's 7827 primes included 31 inert ones, and at each `P0` one of N6's windows included one; both gates now run over split primes only.
    - With T2 strong and no rotation, the boundary is the low side's least value, `5/6 + (2σ − 1)₊ min(1/(6(4σ + 1)), c/(12c + 5 − 4σ))` (H8). So `5/6` needs `σ ≤ 1/2` or `c = 0`: a partial T1 and a partial T3 do not combine to reach it. With the rotation kept the floor is `5/6 + min(c/4, 1/48)` at every `σ`.
    - The goal is still not reached.

## 0. Horizon scan, 2026-10-22

CLAUDE.md asks for a scan at the start of each RH-strand round series. Each item below was read in its arXiv abstract (the arXiv API), except Xu–Sang's 2610.15291v2, whose LaTeX source was read where section 3 quotes it.

- `github.com/openai/math` is at `1581d4c` (`git ls-remote`), as in round 506.
- **arXiv 2610.26835**, Baiying Liu, "Zero-free half-planes for Hecke L-functions over number fields" (v1, 19 October). It extends the cubic-theta argument to cyclotomic fields containing `μ₁₂` and, adapting Xu–Sang's averaged numerator "combining it with a limiting contradiction argument, we obtain the boundary `$B_\flat=0.874886647039964\ldots$`", "the exact infimum of the refined comparison system, unattained by finite chains starting above it", and concludes that "every finite-order Hecke `$L$`-function over every number field is zero-free for `$Re(s)>B_\flat$`". New against the pilot.
- **arXiv 2610.15291v2** (15 October), now by Yuanda Xu and Hejian Sang and titled "Amplified moments and a refinement of the quasi-Riemann hypothesis". The abstract keeps "`$8748867/10000000=0.8748867$`". New version against the pilot (round 506 recorded v1).
- **arXiv 2610.17675v2** (14 October), Xu and Sang, now "A matching lower bound for the sextic large sieve and structured prime moments": "we prove a lower bound of order (AB)^(-epsilon) times (A + B + A^(5/6) B^(1/3) + A^(1/3) B^(5/6)), matching de Faveri's upper bound throughout the full parameter range".
- **arXiv 2610.15989v2**, Yangbo Ye, "Zero density in short strips and short-interval bounds toward Hypothesis S": it uses "the recent quasi-Riemann theorems" as an input.
- **arXiv 2610.18214**, Michel Planat, on the de Bruijn–Newman constant; its abstract "records Raymond's ceiling below `\(0.116398\)` under the distinct `\(7/8\)` zero-free hypothesis".

None of these reaches `5/6`, or claims a boundary below Liu's `0.8748866…`. The Lean community was not searched.

## 1. The floor

The release's low side, as the boundary it gives (README round 503), is

`s₀ = 5/6 + l_x/6 − ℓ/6 + max(0, θb, 2b − l_y)/2 + L/2 + μ/2`,

with `θ = 1/6` (the Gram bound's exceptional term), `L` the completed rows' norm loss and `μ = (M + ℓ − 1)₊` the crossing (round 500). Two of the method's own conditions bound it below:
- the Gram bound's range, "`P_a=Y'^2/Q\ge1.`" (README round 499), which is `b ≥ 0`;
- the compensated probe's geometry: it rescales `X` and `Y` by every slot product, and Xu–Sang state "We will require `\begin{equation}\label{eq:low-geometry} l_x>\ell,\qquad l_y-\ell>11b/6. \end{equation}`".

With `b ≥ 0` the Gram term is at least `b/12`, and `l_x/6 + b/12 = M/12`. So

`s₀ − 5/6 = (M − 2ℓ)/12 + (max(0, b/6, 2b − l_y) − b/6)/2 + L/2 + μ/2 ≥ (l_x − ℓ)/6 ≥ 0`.

**Gate F1** checks the identity and the inequality at 4000 random rational geometries. It also checks that equality holds exactly when `l_x = l_y = ℓ` and `L = μ = 0`, and that the identity agrees with `lowbudget.steps` (round 503) at the 1113 geometries where both are defined. The vertex `(1/3, 1/3, 1/3)` gives exactly `5/6`.

**The theta reading.** In `PAIRING.md` the boundary is `β_b = 5/6 − ℓ/6 + M/12 + L/2`: the amplified Möbius mass reaches the completed rows' energy bound there. The slots gain `ℓ/6`, and the theta function's energy deficit on `Z^M` rows costs `M/12`. With `b ≥ 0` and `l_x > ℓ`, `M = l_x + l_y ≥ 2ℓ`, so in this exponent system the slots' gain does not exceed the deficit, and the base `5/6` stays. That base is the Möbius mass's exponent `1/2 + 1/3` at order 6.

## 2. The second branch: a slot sum at a trivial dual

**Where the loss is attained.** Round 500's dyad program (`crossing.py`) maximizes the energy exponent of Lemma `lem:reflected-energy` over the dyads. On the slice, its second branch `M′ + (1 + 3ℓ′ − 2M′)/4` is what limits `ℓ` to Sang's `1/5`. **Gate F3** finds the maximizing dyad at `(M′, ℓ′) = (2/3, 1/3)`:
- the dual is trivial (`v = ℓ_b = e = 0`) and every slot is active (`z_a = ℓ′`);
- the powerful part has `O = M′ − (1 − ℓ′)/2`;
- `E = O/2 + H + z_a` exactly.

With the powerful part forced to `0`, the maximum is `M′ + 1/9`, at a dyad whose squarefree dual part is again trivial (`v = 0`, cube part `ℓ_b = 2/9`).

Take such a dyad. The release identifies the moving columns as "`\chi_R(nb^3)^3=\chi_R(nb)^3,\qquad \chi_P(nb^3)^{-2}=\chi_P(n)^{-2}1_{(P,b)=1}.`" So at `n = 1` they carry no character of `P`, and each row's completed sum is a fixed multiple of `Σ_P a(P)/√q_P`. The lemma assumes only "`|a(P)|\le1,\qquad |\beta(n,b)|\le1.`", and its bound at `N = 1` is Cauchy–Schwarz, `Z^{z_a}`.

**What `a(P)` is.** By Corollary `cor:marked-reflection`, an active marked prime `q` carries the scalar factor "`\chi_q(\sigma_q)^{-2}(-\omega_{q,0})`", with "`-\omega_{q,0}=\tau_{q,2}^{+}\chi_q(\epsilon_q)^{-2}`" and "`\tau_{p,m}^{\pm}=q_p^{-1/2}\sum_{y\bmod p}\chi_p(y)^m e(\pm y/p),`". That is `γ₂(q)`, the normalized cubic Gauss sum, by the release's "`\gamma_j(c)=q_c^{-1/2}\sum_{v\bmod c}\chi_c(v)^j e(v/c),`". The same scalar has "`\bar\alpha(c)^2`", with "write `$\alpha(a)=a/|a|$`". The primal slot coefficient is "`\overline{\eta(p_i)}W_i(q_{p_i}/P_i)`". The other factors are cubic symbols of fixed elements, the pairwise mark–mark phases and the target's finite-order `η̄`. So, as a function of the slot prime, `a(q)` is `γ₂(q)ᾱ(q)²` times finite-order factors.

**Patterson's bias (gate N1).** Over the ~~7827~~ 7796 split primary primes of norm `≤ 8·10⁴` *(section 14: the 7827 included the 31 inert primes of norm `q² ≤ 8·10⁴`, at each of which `γ₂ = 1` and `α = −1`; the values below are now over split primes only)*, in the pilot's Gauss sums (`composite.py`, `periods.c`):
- `γ₂³ = μα` at every prime (error `1.2·10⁻¹¹`), as in the release's eq. (signal);
- `|Σ γ₂(π)α(π)^k|` is ~~`893`~~ `862` at `k = 0`, against ~~`√n = 88.5`~~ `√n = 88.3`, growing with log-slope ~~`0.77`~~ `0.78` between `2·10⁴` and `8·10⁴`: Patterson's main term `X^{5/6}/log X` *(section 14: the slope is now gated, against `0.74` for `X^{5/6}/log X` there and `0.45` for `√n`)*;
- every twist with `k ≠ 0` stays at square-root size: ~~`112, 91, 160, 43, 49, 34`~~ `143, 122, 129, 74, 80, 65` for `k = −3, …, 3`.

The slot coefficient is the case `k = −2`. So at these sizes its prime sums carry no main term.

**The exponent `σ`.** ~~Write the slot sum's square as `Z^{σ z_a}`.~~ *(Struck in section 7. A bound at the trivial dual alone does not move the dyads' maximum: dyads with a short dual have nearly the same energy. Below, `σ` is the parameter of the second branch `(1 + (4σ − 1)ℓ′ − 2M′)/4`; section 7's dictionary says which hybrid bound gives which `σ`.)*
- The release's bound is `σ = 1`.
- `σ = 2/3` ~~is the cubic large sieve's `(NL)^{2/3}` term at a trivial dual (`N = 1`)~~ *(section 7: is the hybrid bound `N + (NL)^{2/3}`, the `L` term dropped at every dual length, which gate F3 computes)*. The release quotes that sieve from Heath-Brown: "`\{U+V+(UV)^{2/3}\}`". Its `(NL)^{2/3}` term is also the size of Patterson's main term, which the theta-aligned coefficients (`k = 0`) attain.

With the cubic sieve's `L` term dropped for these coefficients, the dyad program's maximum becomes `M′ + max(0, M′ + ℓ′ − 1, (1 + 5ℓ′/3 − 2M′)/4)`. **Gate F3** checks this at 300 random `(M′, ℓ′)` with `ℓ′ ≤ 0.36`; above `ℓ′ ≈ 0.4` another branch appears, which this note does not need. In general the second branch becomes `(1 + (4σ − 1)ℓ′ − 2M′)/4`. *(Section 7: this is the parametrization used below; it does not follow from a bound at the trivial dual.)*

**The low side's least value (gate F2).** Over the whole geometry, with `b ≥ 0`, `l_x ≥ ℓ`, the first-branch crossing at cost `1` and a retained dyad:

`min s₀ = 5/6 + max(0, (2σ − 1)/(6(4σ + 1)))`

The linear programs agree with this to `10⁻¹⁶` at `σ = 0, 1/4, 1/2, 2/3, 3/4, 1`:

| `σ` | least low side | where |
|---|---|---|
| `1` (the release) | `13/15` | `ℓ = 1/5`, round 496's W6b |
| `3/4` | `41/48` | `ℓ = 1/4` |
| `2/3` (the cubic sieve's `(NL)^{2/3}` term) | `28/33` | `ℓ = 3/11` |
| `≤ 1/2` | `5/6` | `l_x = l_y = ℓ ∈ [1/(5 − 4σ), 1/3]` |

Without `l_x ≥ ℓ`, `σ = 0` goes down to `2/3`. That condition is what makes `5/6` the floor.

So the release's low side reaches its floor only with `σ ≤ 1/2`. ~~That means slot sums of angle-twisted cubic Gauss sums over primes of size `X^{3/4}` or less.~~ *(Struck in section 7: such slot sums in every column give `σ = 5/8` and `71/84`; `σ = 1/2` is a square-root sieve `N + (NL)^{1/2}` for the slot coefficients, gate S5 of `slotsplit.py`.)* *(Section 9: `σ = 1/2` also follows from `N + N^{3/4}L^{1/2}`, S5 (c).)* N1 suggests that the slot coefficient's prime sums are near square-root size. The obstacle is the method's bound, not a main term. *(Section 7: beating `(NL)^{2/3}` has to use the coefficients themselves; Dunn and Radziwiłł show that the term is sharp for general coefficients under GRH.)*

## 3. The whole exponent system at 5/6

`fivesixths.py`'s `Five` extends `offslice.OffSlice` (round 499) with:
- round 500's crossing cost on the first branch only;
- the second branch at exponent `σ`;
- a uniform row-sum saving `U^η = Z^{ηh}` on every bin: the bins with `δ ≥ 1/8`, the small bins and the floor bin;
- the small rows' `z`-line `z₀`;
- dropped rows.

**The readings it needs.** Each is a reading of the cited text, in the sense of round 498, not a re-derivation.
- **No rotation.** Xu–Sang impose `h < 2l_y` for the rotated numerator: "The next section therefore imposes `\(h<2l_y\)`: at the critical row scale `\(d=h\)`, the averaged numerator then improves the complete high-side estimate, not just one factor." Their admissibility list files it under "`\emph{Prime supply and numerator amplification.}`". With `ϑ = 0`, the factor "`\(Z^{\vartheta(d/2-l_y)}\)`" is `1`, and the condition does nothing. Round 507 found that on Sang's slice, from `k = 5/2` on, "the best numerator line is `Re w = 1/2`, unamplified".
- **The third Gram term soft**: round 499's S3. The condition's one use is "and hence `$P_a^2/Y'\ll P_a^{1/6}$`".
- **The small rows' `z`-line.** Xu–Sang: "For rows below `\(Z^{d_{\min}}\)`, including the nonprincipal unit rows, the absolute numerator bound and full correction give exponent at most `\(C_b(\beta_*)+h(z_0-1/6)-l_y/2+2d_{\min}\)`", with "`\(z_0=17/50\)`". The release's line for these rows is "`x_r=\beta_*+e,\qquad w_r=1/2,\qquad z_r=17/50,`". Its proof uses four exponents off `u`, "`Q^{-x_r}+Q^{-6z_r} +Q^{4-5x_r-6z_r}+Q^{1-w_r-6z_r}`", the boundary terms on `u`, and the first Euler region's normal convergence. **Gate F6** checks every one of these at `x_r = 5/6`, `w_r = 1/2`, `z_r = 1/6 + 1/100`; the line stays right of `ζ_F(6z)`'s pole at `1/6`.
- Round 498's five readings, `ℓ ≥ 1/6` dropped (rounds 501–502), and Sang's `ℓ ≤ 1/5` replaced by the second branch at `σ`. **Gate F6** also checks that at the vertex the rescaled tuples' exponent `−d + L_σ(d)/2` is at most `0`, so the low side is still taken at `d = 0`.

**Results** (gates F4, F5; `κ` least over `13/18`, `0.7226111` and `3/4`; "no rotation" means the readings above):

| configuration | `σ` | `η` | `z₀` | boundary | at `(l_x, l_y, ℓ)` | walls |
|---|---|---|---|---|---|---|
| round 498's "everything" (Gram removed) | `1` | `0` | `17/50` | `0.8613056` | `(0.3345, 0.4988, 0.1667)` | as recorded |
| Lindelöf + all readings | `1` | `0` | `17/50` | `0.8667866` | `(0.4002, 0.4002, 0.1995)` | as recorded |
| DH + Lindelöf, no rotation | `2/3` | `0.13` | `17/50` | `28/33` | `(0.3636, 0.3636, 0.2727)` | `b > 0`, low side, row loss |
| Sang's counts and fourth moment, no rotation | `1/2` | `0.18` | `1/6 + 1/100` | `5/6` | `(1/3, 1/3, 1/3)` | `b > 0`, low side, `l_x > ℓ`, row loss |
| DH + Lindelöf, no rotation | `1/2` | `0.18` | `1/6 + 1/100` | `5/6` | `(1/3, 1/3, 1/3)` | the same |
| Sang's, no rotation | `1/2` | `0.18` | `17/50` | `0.835` | `(0.3267, 0.3467, 0.3267)` | the small rows |
| DH + Lindelöf, no rotation | `1/2` | `0.16` | `1/6 + 1/100` | `0.8351476` | `(0.3370, 0.3370, 0.3261)` | the floor bin |
| DH + Lindelöf, no rotation | `1` | `0.3` | `1/6 + 1/100` | `13/15` | `(0.4, 0.4, 0.2)` | row loss |

**The row saving the vertex needs (gate F5).** At `(1/3, 1/3, 1/3)`:
- `h = 1`, and round 499's C₀ wall `4/3 − 5l_x/6 − l_y/2 + ℓ/3` is `1`, so `η ≥ 1/6`.
- The floor bin adds half its width: DH counts with Lindelöf reach `5/6` at `η = 0.168` and not at `0.166`.
- Xu–Sang's counts and fourth moment reach it at `0.178` and not at `0.175`, with the bins `E` binding below.

The boundary `5/6` is approached, not attained: `b > 0` and `l_x > ℓ` are strict, and at `σ = 1/2` the second branch is tight there. Liu's and Xu–Sang's limiting contradiction arguments are of that kind.

## 4. What it would take

Within this exponent system, the half-plane `Re s > 5/6` needs both of *(section 8: this assumes round 500's crossing cost `c = 1`; a cheaper crossing is a third route)*:

1. **~~The slot sums at a trivial dual with `σ ≤ 1/2`.~~ A square-root sieve for the slot coefficients (`σ ≤ 1/2`)** *(corrected in section 7)*.
   - ~~The target: `|Σ_P a(P)/√q_P|² ≪ Z^{z_a/2 + ε}` for the release's slot coefficients, which are products of `γ₂(q)ᾱ(q)²` and finite-order factors over the slot primes.~~
   - ~~In one slot, that is `Σ_{q ∼ P} γ₂(q)ᾱ(q)²ψ(q) ≪ P^{3/4 + ε}` over primes. The sources read on this branch bound such sums only through the cubic large sieve, whose `(NL)^{2/3}` term gives `σ = 2/3` and the floor `28/33`.~~
   - *(Section 7: the target is `Σ_{j∼N}|Σ_P a(P)χ_P(j)^{−2}/√q_P|² ≪ Z^ε(N + (NL)^{1/2})` at every dual length `N`, for the release's slot coefficients, which are products of `γ₂(q)ᾱ(q)²` and finite-order factors over the slot primes, times the mark–mark phases. A bound at the trivial dual alone gives nothing, and square-root slot sums in every column give `71/84`.)* *(Section 9: `N + N^{3/4}L^{1/2}` suffices, and only `N < L²` matters, since for `N ≥ L²` the release's factor is already `≪ N`. The `71/84` row is squared slot sums `≪ L^{1/2}`, not square-root size.)*
   - N1 finds no main term at `k = −2`. Dunn and Radziwiłł's corrected large sieve (`CUBIC.md`, section 2) subtracts the theta term and beats `(AB)^{2/3}`, "albeit only for sequences that have substantial cancellations against all non-principal cubic characters".
2. **A row-sum saving `U^η`, `η ≥ 1/6`, on the bins near `a = 1/2`.**
   - The high side bounds each Poisson row's contribution absolutely, then sums over the rows of a bin.
   - At `δ → 0` every row counts (`R = 1`), and that sum is the C₀ wall.
   - A saving there means cancellation in `Σ_u q_u^{−z}ξ̄(u)ζ_F^S(6z)L^S(w, χ_•(u))/L^S(s, ηχ̄_•(u))·𝔥_{η,u,Z}` over the rows `u` (the release's eq. `stage-high-identity`), on lines near `Re s = 1/2`.

The other ingredients are readings of the cited texts (section 3) or the configurations of round 498 (DH counts or Lindelöf on average help, but are not needed: Xu–Sang's own counts and fourth moment reach the vertex at `η ≥ 0.178`).

**Where the walls meet.** At `l_x = l_y = ℓ = 1/3` four walls meet at `5/6`:
- the low side's floor (`l_x = ℓ`, `b = 0`);
- the second branch at `σ = 1/2`;
- the cube-dual branch of section 2, `(1 + ℓ′ − 2M′)/3`, which is `0` at `M′ = 2/3`, `ℓ′ = 1/3`;
- the C₀ wall at `η = 1/6`.

So `5/6` is a natural point of the method, not an arbitrary target. By gate F1, going below it in this exponent system needs a geometry without `l_x > ℓ` or `b ≥ 0`, or a low side without the exceptional Gram term. Rounds 504–505 found that removing that term removes the principal residue with it.

## 5. Outcome, register entry and signals

**Outcome.** The goal is not reached. This note proves no new zero-free region. It maps what the release's method needs for `5/6`, and finds `5/6` to be that method's floor.

**Check 9 (a), scope.** Every boundary, floor and threshold here is a statement about the pilot's model of the release's exponent system (rounds 496–508), with the readings of section 3. That includes "the floor" and "needs".
- "The floor" assumes `b ≥ 0`, `l_x > ℓ` and the exceptional term `θ = 1/6`.
- "Needs" is relative to the configurations computed: twelve programs in F4 and F5, and the low side's linear programs in F2.
- The statement that the sources read bound the slot sums only through the cubic large sieve is scoped to the release, Xu–Sang's v2 and the notes on this branch. The literature on prime sums of cubic Gauss sums was not surveyed, so no claim is made about what it contains. *(Section 7: surveyed since, in Heath-Brown 2000 and Dunn–Radziwiłł 2024.)*

**Check 9 (b), register.** STRUCTURAL-REVIEW §6, the sub-entry "Below `7/8` in the release's exponent comparison", gets a bullet "The release's exponent system at `5/6`" with two targets.
- **T1, ~~trivial-dual slot sums with `σ ≤ 1/2`~~ a square-root sieve for the slot coefficients, `σ ≤ 1/2`** *(corrected in section 7)* *(section 9.5: the weaker `N + N^{3/4}L^{1/2}` suffices)*.
  - Socket: the `L` term of Lemma `lem:hybrid-energy` inside the second branch of Lemma `lem:probe-row-norm`, which is `fivesixths.py`'s gate F3. *(Section 7.6 widened it to the `(NL)^{2/3}` term. With the trilinear bound of 9.1 the `L` term is gone, so the socket is that term.)*
  - Attack notes:
    1. a corrected cubic large sieve, in the sense of Dunn–Radziwiłł's Proposition 9.1, for angle-twisted Gauss-sum coefficients, which do not attain the `(NL)^{2/3}` term *(section 9.2: that proposition assumes their axiom (3.2), ~~which for prime-supported coefficients is of GRH strength: circular here as stated~~ which for the slot coefficients either fails outright or asks for a zero-free region `Re s > 1/2 + η`, `η ≤ 1/4`, for a fixed `L`-function of the release's family: unusable as stated, 9.7)*;
    2. a Type I/Type II decomposition of the slot sums, whose Type I part has no pole for `k ≠ 0`;
    3. slot structures other than single primes, which the compensation would have to accommodate.
- **T2, a row-sum saving `U^{1/6}` near `a = 1/2`.**
  - Socket: the bins' sums in Lemma `lem:bin-contour-accounting` and Xu–Sang's eq. `full-exponent` at `R = 1`.
  - Attack notes:
    1. the diagonal of the ratio average over `u`, where `ξ`, nonprincipal at every prime of `S`, may vanish;
    2. the sextic large sieve over the rows, whose limits Xu–Sang's matching bound now fixes;
    3. a first moment of the reflected numerator with the inverse polynomial in place of Sang's fourth moment.

**Check 9 (c), signals.** The signal is unchanged: the release's probe. T1 bounds Gauss sums at primes. They do not involve the target's zeros, so the input is auxiliary, not circular. T2 concerns the sum over the twisted rows near `Re s = 1/2`. The hypothetical zero sits near `5/6`, not on those lines, so T2 is auxiliary too.

**The machinery checklist.**
- Surveyed:
  - the release's Corollary `cor:marked-reflection`, Proposition `prop:completed-reflection`'s scalar, Lemmas `lem:hybrid-energy`, `lem:reflected-energy`, `lem:probe-row-norm` and `lem:compensated-absolute-local-bounds`, the local Euler regions, and Definition `def:stage-high-data`;
  - Xu–Sang's v2 sections on the low estimate, the numerator and admissibility;
  - the pilot's Gauss sums for Patterson's bias.
- Not surveyed:
  - the literature on cubic Gauss sums over primes *(section 7: surveyed since)*;
  - ratio averages over sextic families;
  - large values of Guth–Maynard type for the rows near `1/2`.

## 6. Reproduce

From this directory:

```
python3 fivesixths.py periods_w_8e4.txt    # gates F1-F6 and N1, about 15 s
```

`periods_w_8e4.txt` is the prime data of `PAIRING.md` section 7 (`./periods w 80000`). Without it, N1 is skipped and reported. The script imports `crossing.py`, `offslice.py`, `levers.py` and `lowbudget.py` from `../wall78`.

In session runs these perturbations fail the gates shown:
- the exceptional exponent `θ = 1/12` fails F1;
- the second branch's coefficient raised by `0.02` fails F4 and F5;
- the floor bin without the row saving fails F4 and F5;
- the release's pieces in place of the `L`-free ones fail F3;
- the sextic `γ₁` in place of `γ₂` fails N1;
- the second branch's constant `1/7` in place of `1/8` fails F2.

## 7. Follow-up: the literature, the slot product split in two, and what `σ` means

Same day, same branch. The gate script is `slotsplit.py` (gates S1–S5; with sections 8 and 9, S1–S8, about 70 s; `python3 slotsplit.py`). Every number is a statement about the pilot's model of the release's exponent system, as in sections 1–5.

### 7.1 The literature on T1

Surveyed on 2026-10-22 by web search. Two sources were read: Heath-Brown's abstract in the Oxford ORA record, and Dunn and Radziwiłł's arXiv text (2109.07463v3), whose quotes below are from its PDF text with the extraction's symbol damage repaired.
- **Heath-Brown, "Kummer's conjecture for cubic Gauss sums" (2000).** For the sum over the integers `c ≡ 1 (mod 3)` of `ℚ(√−3)` with `N(c) ≤ X` of `g̃(c)Λ(c)(c/|c|)^l`, the abstract gives `≪_ε X^{5/6+ε} + |l|X^{3/4+ε}`, and adds: "When $l=0$ it is conjectured that the above sum is asymptotically of order $X^{5/6}$, so that the upper bound is essentially best possible." For `l ≠ 0`, which includes the slot coefficient's angle `ᾱ²`, the bound is still `X^{5/6+ε}`. The `X^{3/4}` term is the angle's cost, not a bound for the sum.
- **Dunn and Radziwiłł, "Bias in cubic Gauss sums: Patterson's conjecture".**
  - Under GRH, Theorem 1.1 gives Patterson's asymptotic, and Theorem 1.3 gives `o(X^{5/6}/log X)` for the powers `g̃(ϖ)^k`, uniformly in `1 < |k| ≤ X^{1/100}`. Neither saves a power of `X` below `5/6`. *(Section 10: Patterson's first moment is since proved without GRH, in OpenAI's preprint.)*
  - The abstract: "we show that Heath-Brown's cubic large sieve is sharp up to factors of $X^{o(1)}$ under the Generalized Riemann Hypothesis".
  - Their corrected sieve, eq. (1.13), allows them "to beat the exponent $(AB)^{2/3}$, albeit only for sequences that have substantial cancellations against all non-principal cubic characters", with a small fixed saving `δ`.
- **For T2 (found by search, not read; as the search results summarize them):** ~~ratios conjectures over cubic families have been proved with one shift by multiple Dirichlet series, under GRH: Gao and Zhao, arXiv 2311.08626 (cubic Hecke `L`-functions of prime moduli over the Eisenstein field), and Čech, arXiv 2110.04409 (real characters).~~ *(Section 9: misfiled, since Čech's family is not cubic. From the two abstracts, read since: Gao and Zhao develop the ratios conjecture with one shift "for the family of cubic Hecke $L$-functions of prime moduli over the Eisenstein field using multiple Dirichlet series under the generalized Riemann hypothesis"; Čech considers "the family of real Dirichlet characters", and "All of the results are conditional under the Generalized Riemann hypothesis.")* Here GRH for the rows' family is stronger than the conclusion sought, so those results are not usable as stated.

### 7.2 What `σ` means (gate S5)

Section 2 called `σ` the exponent of the slot sum at the trivial dual. That is false. A bound at the trivial dual alone does not move the dyads' maximum, because dyads with a short dual have nearly the same energy.

What the second branch `(1 + (4σ − 1)ℓ′ − 2M′)/4` needs is a hybrid bound for `Σ_{j∼N} |Σ_P a(P)χ_P(j)^{−2}/√q_P|²`, at every dual length `N`. Gate S5 replaces the release's factor in round 500's dyad program by each bound below. *(Section 9: S5 then covered the table's last three rows, and "never exceeds" is checked at S1's points, `ℓ′ ≤ 0.36`; only the dual lengths `N < L²` matter. The corrected table is in 9.5.)* For each it checks three things:
- the program never exceeds the second branch with the `σ` shown;
- it equals that branch at the low side's optimum *(9.7: there both are `0`, so this tested nothing. S5 now checks equality at four points where the branch is positive, for rows (a)–(d), and that row (e) stays below it there)*;
- the least low side agrees between F2's linear program and the exact program on a grid.

| hybrid bound | `σ` | least low side |
|---|---|---|
| the release's `N + L + (NL)^{2/3}` | `1` | `13/15` |
| the slot-split bound, `min(·, N L^{2/3})` (section 7.3) | `3/4` | `41/48` |
| ~~every column's slot sum at square-root size~~ *(mislabelled: every column's squared slot sum `≪ L^{1/2}`, section 9.5)*, `min(·, N L^{1/2})` | `5/8` | `71/84` |
| the `L` term dropped, `N + (NL)^{2/3}` | `2/3` | `28/33` |
| a square-root sieve, `N + (NL)^{1/2}` | `1/2` | `5/6` |

~~So the low side's floor needs a square-root cubic large sieve for the slot coefficients. Slot sums at square-root size in every column (prime sums `≪ X^{3/4}`, beyond Heath-Brown's `X^{5/6}`) would give only `71/84`.~~ *(Struck in section 9, false as written. `σ = 1/2` follows from the weaker `N + N^{3/4}L^{1/2}` (S5 (c)). The `71/84` row is squared slot sums `≪ L^{1/2}`, that is slot sums `≪ L^{1/4}` (before the `1/√q_P` normalization, `≪ L^{3/4}`), not square-root size; square-root cancellation in every column gives `5/6` (S5 (e)). And the slot sums are not products of prime sums: the pair phases couple the slots.)* Dunn and Radziwiłł's sharpness result says `(AB)^{2/3}` cannot be improved for general coefficients (their lower bound assumes GRH). A bound `N + (NL)^{1/2}` therefore has to use the coefficients themselves: the angle `ᾱ²`, which removes Patterson's main term at the primes measured (N1), and the slots' product structure.

### 7.3 The slot-split bound (gates S1, S2)

The release keeps the slot coefficients' structure up to the norm step:
- "The physical slot sets remain disjoint and their separated coefficients are product-form." (paper.tex lines 8204–8205).
- Its eq. `reflection-pair-phase` (lines 7443–7449): "`For distinct active good primes \(p,q\), Equation~\eqref{eq:reflection-cross-prime-phase} and cubic reciprocity give`" `\chi_p(q)^{2j_p+2}\chi_q(p)^{2j_q+2} =\left(\frac qp\right)_3^{j_p+j_q+2}`, and "`For an active mark the exponent is \(j_q=0\)`". So two active marks carry `(q/p)_3^2`.
- "Row-row phases are row scalars, mark-mark phases are tuple scalars, and their interactions with frozen primes depend on only one of those sets." (lines 7464–7466). "The angular conductor scalar factors in the same way."
- It then gives the structure up: "`The function \(a\) need not retain product form at this norm step.`" (lines 7966–7967).
- Its slots: "`Choose a fixed even integer \(K\) with`" `\ell_i=\frac{\ell}{K}\quad(1\le i\le K)` (lines 16246–16250).

**The bound.** In the proof of Lemma `lem:hybrid-energy`, each column `j` meets the inner sum `Σ_{P′} a_{D,r}(P′)q_{P′}^{−1/2}χ_{P′}(j)^{−2}1_{(P′,ht)=1}`. The release bounds the sum of its squares over the columns by its eq. `cubic-large-sieve` (lines 7491–7497), giving the factor `N/r_0 + L/D_0 + (NL/(r_0D_0))^{2/3}` (lines 7632–7640).

Split the active slots that remain after the Möbius divisor `D` into two halves of nearly equal length, `P′ = AB`. For a fixed column, the column character, the divisor's phases, `χ_{P′}(r)^{−2}`, the class characters modulo `M_ref²` and the coprimality masks are one-prime factors. The mark–mark phases across the halves multiply to `(B/A)_3^2`. So the inner sum is `Σ_{A,B} x_j(A)y_j(B)·conj((B/A)_3)`. The same cubic sieve in `(A, B)` bounds its square by `(L_A + L_B + (L_AL_B)^{2/3})Z^ε‖x_j‖²‖y_j‖²`, about `(L/D_0)^{2/3}` for balanced halves.

Summed over the `≪ N/r_0` columns, the factor may be replaced by its minimum with `(N/r_0)(L/D_0)^{2/3}Z^{O(ℓ/K)}`. That bound also increases when `D_0, r_0` are replaced by `1`. When fewer than two active slots remain, the release's factor is kept, and then `L/D_0 ≤ Z^{ℓ/K}`. With `K` large, the lemma's factor becomes `min{N + L + (NL)^{2/3}, N L^{2/3}}`. In the energy of Lemma `lem:reflected-energy`, `u = min{v, z_a, (v + z_a)/3}` becomes `max{u, z_a/3}`.

**What it gives.**
- **S1:** the dyads' maximum is `M′ + max(0, M′ + ℓ′ − 1, (1 + 2ℓ′ − 2M′)/4)`.
  - It holds as an upper bound everywhere sampled, with equality when `M′ ≥ 1/2 − ℓ′/3 + 1/100`.
  - At `(2/3, 1/3)` the excess is `1/12`, against the release's `1/6`, and the maximum moves from the trivial dual to `v = z_a/3`.
- **S2:** the least low side is `41/48 = 0.8541667`, at `(l_x, l_y, ℓ) = (1/4, 1/2, 1/4)`, against the release's `13/15`. *(Section 9: at `(M, ℓ) = (3/4, 1/4)` the low side is the same for every `l_x ∈ [1/4, 3/8]`. Xu–Sang's `l_y − ℓ > 11b/6` fails at the point named and holds for `l_x > 21/64`: S2.)*

**Scope.** This is a written argument checked against the release's text at the lines cited. It has not been refereed or formalized. *(Superseded the same day by the trilinear split, `σ = 2/3`: section 9.1.)*

### 7.4 The ladder (gate S3)

The release's unconditional inputs here are Xu–Sang's counts and fourth moment, the readings of section 3, and Sang's rotation. With them, the boundary is `0.8748866` at `σ = 1`, `3/4` and `1/2` alike *(and at `2/3`: S3, section 9)*. The walls are the bins `δ ≥ 1/8` ("`E`") and the low side without row loss. So the slot-split bound does not move the release's boundary by itself.

With a uniform row saving `U^{1/10}`, no rotation and the small rows' line at `1/6 + 1/100`:
- `13/15` at `σ = 1`;
- `41/48` at `σ = 3/4`;
- *(section 9)* `0.8537843` at `σ = 2/3`, with the bins `E` binding.

### 7.5 The vertex's bins (gate S4)

At `(1/3, 1/3, 1/3)`, with density-hypothesis counts `R = 1 − δ`, Lindelöf and no rotation, the bins at `x = 1/2` have endpoint `1 − δ/3 − s₀` (exact). So `s₀ = 5/6` needs a saving of at least `1/6 − δ/3` on every bin with `δ < 1/2`. That is more than those counts give: either counts below `5/6 − 2δ/3` or cancellation among the rows.

In the program, savings `U^{3/10}` on the floor bin and the small bins alone stop at `31/36`, with the bins `E` binding. `U^{1/5}` on every bin gives `5/6`.

### 7.6 The targets, corrected

- **T1** (`σ ≤ 1/2`): the square-root sieve `Σ_{j∼N}|Σ_P a(P)χ_P(j)^{−2}/√q_P|² ≪ Z^ε(N + (NL)^{1/2})` for the release's slot coefficients, at every dual length. *(Section 9: `N + N^{3/4}L^{1/2}` suffices, and only `N < L²` matters; 9.5 restates T1.)*
  - Socket: unchanged (F3's `L` term), widened to the `(NL)^{2/3}` term.
  - Known here: `σ = 3/4` by the slot-split bound (7.3). *(Now `σ = 2/3`, by the trilinear split of section 9.1.)*
  - Attack notes:
    1. ~~a trilinear split that treats `(j, A)` as one modulus. With `B`'s character `(B/jA²)_3` it needs a cubic large sieve over cube-free moduli. If it held with the plain sieve's shape, it would drop the `L` term, giving `σ = 2/3` and `28/33`.~~ *(Struck in section 9, false as written: `B`'s character is `conj((B/jA)_3)`, whose modulus `jA` is squarefree, so the plain sieve applies, and the split gives `σ = 2/3` and `28/33`: section 9.1, gate S8.)*
    2. Dunn–Radziwiłł's corrected sieve for the angle-twisted coefficients: by eq. (1.13), a small power below `(NL)^{2/3}`. *(Section 9.2: its Proposition 9.1 assumes their axiom (3.2), ~~of GRH strength for prime-supported coefficients: circular here as stated~~ which for the slot coefficients either fails outright or asks for a zero-free region `Re s > 1/2 + η`, `η ≤ 1/4`, for a fixed `L`-function of the release's family: unusable as stated, 9.7.)*
    3. slots over squarefree or rough integers, where Patterson's Kubota series bounds the twisted sums at `X^{3/4}` by its functional equation. The compensation and the high side's prime-factor moments would have to be redone.
  - ~~In every source surveyed (7.1), the `(NL)^{2/3}` term is sharp for general coefficients, and no bound below `X^{5/6}` is proved for prime sums of twisted cubic Gauss sums, even under GRH.~~ *(Struck in section 9, false as written. Heath-Brown's abstract, the only text of his read, says nothing on that term, and Dunn and Radziwiłł quote him: "It seems possible that the term (AB)^{2/3} could be removed with further effort". Their own lower bound, under GRH, shows the term sharp for general coefficients. Their Theorem 1.3 gives `o(X^{5/6}/log X)` under GRH: below `X^{5/6}`, though not by a power. No power saving below `X^{5/6}` was found in the two sources read.)*
- **T2:** on the high side at the vertex, a saving `U^{max(0, 1/6 − δ/3)}` on every bin with `δ < 1/2`, beyond what density-hypothesis counts give, and `U^{1/6}` plus the floor bin's half-width on the floor bin.
  - The saving can come from counts below `5/6 − 2δ/3` or from cancellation among the rows.
  - The floor bin holds the generic rows (`R = 1`), so there, in this model, the saving can only come from cancellation among them.
  - ~~Ratio averages over cubic families are proved by multiple Dirichlet series only under GRH (7.1).~~ *(Struck in section 9: unscoped, and Čech's family is real characters. The two papers found prove their ratios results under GRH, by their abstracts.)*

**Check 9.**
- (a) Scope: "surveyed" means the two sources read in 7.1; the ratios papers were found, not read. "Needs" is relative to the hybrid bounds of S5 and the configurations of S3–S4.
- (b) The register entry is corrected with strikes and markers.
- (c) The signals are unchanged: T1 and T2 are auxiliary inputs.

**Outcome.** The goal `Re s > 5/6` is still not reached, and no new zero-free region is proved. This section adds:
- an improvement of the release's second branch from `σ = 1` to `σ = 3/4`, by the written argument of 7.3, which alone does not move the boundary *(to `σ = 2/3` by section 9.1's trilinear split, which alone does not move it either)*;
- a correction of what `σ = 1/2` requires;
- the finding that the vertex's high side needs more than density-hypothesis counts give.

## 8. The crossing cost, a third lever

Same day. Gates S6 and S7 of `slotsplit.py`.

**What it is.** Round 500 derived the crossing cost from the release's proof of Lemma `lem:probe-row-norm`. Crossing the slice `M + ℓ = 1` by `μ` costs `μ/2` on the low side (`c = 1`). The cost is the first branch `M′ + ℓ′ − 1` of the dyads' maximum: the column term `NB` of the factor `K + NB` in Lemma `lem:hybrid-energy`, where the dual is longer than the rows.

The release states the slice in two places only:
- in that proof: "Since $M'+\ell'-1=-3d$, direct subtraction gives" (paper.tex line 8246);
- at its fixed geometry: "M=l_x+l_y=\frac56,\qquad M+\ell=1." (line 6864).

**What a cheaper crossing would give** (S6). The settings are: `σ = 3/4` (the slot-split bound), no row saving, Sang's rotation, round 502's reading that drops `l_y < 1/2`, and the program's cap on `μ` raised from `1/2` to `2`. Both of the last two matter. *(Section 9: S6 now runs at the trilinear `σ = 2/3`, with the same numbers. The settings also include round 498's readings, which matter too: without them `c = 0` gives `0.8700000`, with the principal edge binding, S6.)* In session runs, keeping `l_y < 1/2` gives `0.8504534` at `c = 0`, and keeping the cap at `1/2` gives `0.8436087`. Round 502 found `l_y < 1/2` used only for a slope bound, which holds for `l_y < 1` (its gate F3). *(Section 14: the settings also include the third Gram term soft, round 499's S3 reading, which `slotsplit.cross_cfg` sets.)*

| crossing cost `c` | boundary |
|---|---|
| `1` (the release) | `0.8748866` |
| `0.15` | `0.8725510` |
| `0.1` | `0.8615362` |
| `0.05` | `0.8486654` |
| `0` | `5/6` |

At `c = 0` the low side reaches its floor on the ray `l_x = l_y = ℓ = t`:
- the second branch at `σ = 3/4` is `(1 − 2t)/4`, which is `≤ 0` for `t ≥ 1/2`;
- the C₀ wall `4/3 − t` is at most `5/6` there.

The optimum found is `t = 0.5572`, with `M + ℓ = 1.67`; the bins `E` bind as well. *(Section 9: the two bullets hold for `t ≥ 1/2`, but the bins `E` hold only from a threshold `t* ∈ (0.557239, 0.557240)` on (bisection, S6; 9.7). On the ray at `κ = 3/4` the boundary is `0.8786610` at `t = 1/2`, `0.8390211` at `t = 0.55` and `0.8333645` at `t = 0.5572`, each with `E` binding, and `5/6` at `t = 0.56` (S6). So `c = 0` reaches `5/6` on the ray for `t ≥ t*` only.)* With the release's `σ = 1`, the second branch `(1 − t)/4` vanishes only at `t = 1`, and `c = 0` gives `5/6` at `(1, 1, 1)` *(section 9: the corner of the model's length box `[0, 1]³`, which has no source in the release's Definition `def:stage-high-data`, and only with `μ = 2`, the raised cap; with the cap at `1.9` the program gives `0.8350000`, S6)*. So in this model a free crossing reaches `5/6` with neither T1 nor T2, ~~and a cost above about `0.16` buys nothing (round 499's break-even)~~ *(struck in section 9: in S6's configuration `c = 0.16` gives `0.8744704` and `c = 0.165` gives `0.8748866`, the release's value, so the break-even lies between them; `0.16` was round 499's configuration)*.

**`c = 0` is exactly T3** (gate S7). Replace the quadratic sieve's factor `K + NB` by `K` in round 500's dyad program. Then its maximum has no first branch: it is `M′ + max(0, (1 + 3ℓ′ − 2M′)/4)` at 300 random `(M′, ℓ′)` in `[0.3, 2] × [0, 1]`, and at most `M′ + max(0, (1 + 2ℓ′ − 2M′)/4)` with the slot split. So removing the column term leaves no further branch in the dyads, and the program's `c = 0` is that removal. (With the column term, the maximum on the ray `(2t, t)` is the first branch `3t − 1` for `t ≥ 0.4`. The other branch that F3 avoided above `ℓ′ ≈ 0.4` also comes from the column term: in a session run, its maximizing dyads have a dual longer than the rows, `v > H`. It disappears with the column term.) Keeping the column term in S7's check fails it, in a session run.

**Scope.** Far across the slice, the model's admissibility rests on Xu–Sang's conditions and on the pilot's high side extended there. The release's lemmas are stated for its fixed geometry and were not re-derived at `M + ℓ ≈ 1.7`. Round 496 lists what the model leaves out: "the intermediate range, small and large rows, the frequency extension, and the prime supply against the capacities". The numbers for small `c` are statements about the model, not about the release's argument there.

**Target T3: the column term.** At round 500's first-branch dyad (`O = 0`, `H = M′`, `z_a = ℓ′`, `v = T`), the squarefree dual has length `T = 2M′ + ℓ′ − 1`, longer than the rows' `H = M′`. The quadratic large sieve then charges `K + N ≈ N`.
- The target: a bound `Σ_{k∼K}|Σ_{n∼N} γ(n)χ_k(n)³|² ≪ Z^ε K Σ|γ(n)|²` for `N > K`, for the release's dual coefficients `γ` (the reflection's coefficients times the slot sums). That would make `c = 0`.
- The quadratic large sieve's column term is attained by a coefficient aligned with one row's character. So for general coefficients `N` cannot be improved, and such a bound has to use the coefficients themselves. For coefficients with independent random phases the expected size is `K Σ|γ|²`, with no column term.
- Attack note: a corrected quadratic large sieve, in the sense of Dunn–Radziwiłł's eq. (1.13), for the reflection's metaplectic coefficients twisted by the slot sums.
- Signals (Check 9(c)): auxiliary, like T1.

**Outcome.** The goal is still not reached. The routes to `5/6` in the model are now three:
- T1 and T2 at the vertex `(1/3, 1/3, 1/3)` (sections 4 and 7);
- T3 alone across the slice, with the slot-split bound (this section);
- combinations of partial inputs. For example, `c = 0.05` with a row saving `U^{1/20}` gives `0.8442662` (a session run of S6's program without rotation, with the small rows' line at `1/6 + 1/100`).

Each needs a bound that beats a large sieve that is sharp for general coefficients.

## 9. The trilinear split, the slot coefficient as a Gauss sum, and the review of sections 7–8

Same day. Gate S8 of `slotsplit.py` is new, and gates S2–S7 are extended. A fresh-context hostile review of sections 7–8 and `slotsplit.py` returned one major finding, six minor and ten cosmetic. Each was checked directly before it was accepted (9.4). Every number is a statement about the pilot's model of the release's exponent system, as in sections 1–8.

### 9.1 The trilinear bound: `σ = 2/3`

Section 7.6's first attack note gave `B`'s character in a trilinear split as `(B/jA²)_3`, and concluded that the split needs a cubic large sieve over cube-free moduli. That is false. In column `j`:
- the half `B` carries its column factor `χ_B(j)^{−2}` (paper.tex line 1792), and the release has "`for a good prime $p\notin S$, one has $(x/p)_3=\chi_p(x)^2$`" (lines 1905–1906), so the factor is `conj((j/B)_3)`;
- the mark–mark phases across the halves multiply to `conj((B/A)_3)` (section 7.3);
- cubic reciprocity turns their product into `conj((B/jA)_3)`. The modulus `jA` is squarefree, because the factor `conj((j/A)_3)` vanishes unless `(j, A) = 1`.

**The bound.** For fixed `h, t, D, r`, the release's proof of Lemma `lem:hybrid-energy` notes that "`the \(P'\)-coefficients are independent of \(j=c'm\)`" (lines 7622–7623), and it sums over the columns with "`Cubic reciprocity, conjugation, and Equation~\eqref{eq:cubic-large-sieve}`" (lines 7632–7633). Write column `j`'s inner sum as `Σ_A x(A)conj((j/A)_3)·Σ_B y(B)conj((B/jA)_3)`, where `x` and `y` carry each half's one-prime factors and inner phases.
1. Cauchy–Schwarz in `A` costs `Σ_A|x(A)|²`, which is `≪ Z^ε` by the release's ideal count (line 7623).
2. The rows `m = jA` have norm up to about `N L_A`, and each occurs at most `d(m)` times. The release's eq. `cubic-large-sieve`, "`where both stars mean squarefree in \(\mathcal O\), and the coefficients are arbitrary complex numbers`" (lines 7491–7499), bounds the sum over the columns by `Z^ε(N L_A + L_B + (NL)^{2/3})`.
3. The slots have one scale: "`Put \(P_i=P=Z^{\ell/K}\).`" (line 16253). So when `L > N`, `L_A` can be chosen within a factor `Z^{ℓ/K}` of `(L/N)^{1/2}`; when `L ≤ N`, take `L_A = 1`. Either way the bound is `Z^{ε + O(ℓ/K)}(N + (NL)^{2/3})`. Like the release's, it increases when `D_0, r_0` are replaced by `1`.

That is the factor with the `L` term dropped: the second branch at `σ = 2/3`, and the least low side `28/33` (S5's row (b)). Gate F3 of `fivesixths.py` checks the dyads' maximum `M′ + max(0, M′ + ℓ′ − 1, (1 + 5ℓ′/3 − 2M′)/4)`. The bound supersedes the slot split's `σ = 3/4`.

**Gate S8** checks the ingredients directly in `Z[ω]`, with cubic residue symbols computed by Euler's criterion:
- (i) at 2000 random triples of split primes of norm below `4000`, cubic reciprocity holds, and the half's character equals `conj((B/jA)_3)` at every triple. The struck `jA²` form agrees at ~~674~~ 673 *(section 13: the count after the second round's sweep)*, about a third, as chance predicts. With the column factor unconjugated (a session sabotage run), the identity holds at 673 and the gate fails. *(Section 13: in that run the struck form holds at all 2000 triples, so `(B/jA²)_3` is exactly what the unconjugated column factor gives.)*
- (iii) `min_a max(v + az, (1 − a)z, 2(v + z)/3) = max(v, 2(v + z)/3)` on a grid, and a split in eighths of the slots costs at most `z/8`.

**What it moves.**
- With the release's inputs and no row saving: nothing. The boundary stays `0.8748866` at `σ = 2/3` (S3).
- With a uniform row saving `U^{1/10}`, no rotation and the small rows' line at `1/6 + 1/100`: `0.8537843`, with the bins `E` binding, against `41/48 = 0.8541667` at `σ = 3/4` (S3).
- Section 8's crossing-cost table is unchanged at `σ = 2/3` (S6).

**Scope.** A written argument checked against the release's lines, at the rigour of section 7.3. It has not been refereed or formalized.

### 9.2 The slot coefficient is a composite Gauss sum

For an active mark the release gives "`\(-\omega_{q,0}=\tau_{q,2}^{+}\chi_q(\epsilon_q)^{-2}\)`" (line 7429). Its eq. `reflection-cross-prime-phase` gives `\chi_p(\sigma_p)^{-2}\omega_{p,j} =\xi_{p,j}\chi_p(c/p)^{2j+2}`, with "`a scalar $\xi_{p,j}$ of absolute value one, depending on $p,j$ but on no other active prime`" (lines 2269–2273). Over the active marks of `P`:
- the one-prime parts multiply to `Π_q τ⁺_{q,2}`, times finite-order factors;
- the cross parts multiply to the pair phases `χ_p(q)²χ_q(p)²` (eq. `reflection-pair-phase` at `j_p = j_q = 0`).

By the Chinese remainder theorem, `τ_{c₁c₂,2} = χ_{c₁}(c₂)²χ_{c₂}(c₁)²τ_{c₁,2}τ_{c₂,2}` for coprime `c₁, c₂`. So the tuple's Gauss-sum part is `γ₂(P)`, the release's "`\gamma_j(c)=q_c^{-1/2}\sum_{v\bmod c}\chi_c(v)^j e(v/c),`" (line 642) at the composite modulus `P`. With the angle, which is multiplicative,

`a(P) = γ₂(P)ᾱ(P)²ψ(P)ΠW_i`, with `ψ` of finite order (the fixed elements' characters and the target's `η̄`).

In column `j`, `γ₂(P)χ_P(j)^{−2} = γ₂(j; P) := q_P^{−1/2}Σ_v χ_P(v)²e(jv/P)` when `(j, P) = 1`. So each column's slot sum is `Σ_P γ₂(j; P)ᾱ(P)²ψ(P)ΠW_i/√q_P`: shifted cubic Gauss sums, twisted by an angle, over the products of one prime from each active slot.

**Gate S8(ii)** checks the CRT identity at 25 random pairs of split primes of norm below `400`, by summing over `Z[ω]/pq` directly. The error is `1.6·10⁻¹⁵`; with the conjugate phase it is at least `1.73`. Gate N3 (9.3) measures a model of these sums: over all squarefree `P` of one norm range, inert primes included, with no slot windows or weights, and with `α^k` in place of `ᾱ²ψ`.

**Dunn and Radziwiłł's corrected sieve, as stated, ~~is circular here~~ does not apply here (Check 9(c)).** *(9.7: the axiom's instances and strength were misdescribed below; the corrected account follows the strike.)*
- Their eq. (1.13) is stated for sequences of this shape, `β_b g̃(b)`. It lets them "beat the exponent $(AB)^{2/3}$, albeit only for sequences that have substantial cancellations against all non-principal cubic characters".
- Its precise form, Proposition 9.1, assumes `β ∈ C_η(B, w)` with `0 < η ≤ 1/4`. Their Definition 3.1 makes this an axiom, eq. (3.2): ~~square-root~~ cancellation `(A/N(u))^{1/2+η+ε}` against every angle `(a/|a|)^ℓ`, every `N(a)^{it}` and every cubic character `(k/a)_3`, the trivial ones aside. *(9.7: with `η > 0` that saves `1/2 − η`, not square-root cancellation. With the PDF text's symbols restored, the condition reads "provided that ℓ ≠ 0, or if ℓ = 0, then provided that k ≠ ■", where ■ is their notation for an element of the form `b³`.)*
- They add: "The Generalized Riemann Hypothesis is used to show that axiom (3.2) above holds for sequences of interest to us".
- ~~For `β` supported on products of slot primes, the axiom asks for prime sums of Hecke characters over `ℚ(ω)` that cancel down to `P^{1/2+η}` in every slot. For the cubic characters among them, which belong to the release's own family, that amounts to a zero-free region `Re s > 1/2 + η`: more than the conclusion `5/6` sought.~~ *(False as written, 9.7: at `ℓ = 0` the instances are not cubic characters.)*
- Their sequence is `β = c/g̃`. For the slot coefficient `a(P) = γ₂(P)ᾱ(P)²ψ(P)ΠW_i`, `β` therefore carries the angle `ᾱ²`. It also carries `(λ/·)_3`, since `γ₂(π) = (λ/π)_3 g̃(π)` between the release's additive character `e(z) = exp(2πi Tr(z/λ))` (paper.tex lines 608–611) and theirs (checked at 21 primes in a session run). So at `ℓ = 0` the axiom's sums run over prime products of Hecke characters of infinite order.
- At `ℓ = 2` the twist cancels the angle, and `k` runs over all primary elements, cubes included. The sums then run over prime products of a finite-order character. The slot primes lie in the ray class `1_T`, and "`On $1_T$ one has $\theta(p)=1$ for every $\theta\in\widehat T$`" (paper.tex lines 6909–6910). If some `k` makes that character principal on the slot primes, the sum has a main term of size about `A`, and (3.2) fails outright. Whether that happens depends on whether the 3-adic supplementary phase factors through `T`; this note does not settle it.
- Otherwise (3.2) asks for cancellation to `P^{1/2+η}` in the prime sums of a fixed finite-order Hecke `L`-function of the release's family. That is a zero-free region `Re s > 1/2 + η`, at least `Re s > 3/4` since `η ≤ 1/4`: more than the conclusion `5/6` sought, though not GRH.
- Either way, the route is unusable as stated.

The register records the route with this signal.

### 9.3 The coefficient models (gates N2, N3 of `columnterm.py`)

Commits `19f70fbc` and `ffb66062`, the same day. Both gates measure models of the coefficients at small norms. They are evidence about those models, not bounds.

**The theta term in the columns (N3).** Let `R_k = Σ_j|Σ_P γ₂(P)α(P)^kχ_P(j)^{−2}|²/(#columns·Σ|coefficient|²)`, over the squarefree `P` of norm in `(L/2, L]` and the squarefree columns `j` of norm `≤ N`, with `χ_P(j)^{−2} = conj((j/P)_3)`.
- On average over the columns, the untwisted sum carries Patterson's theta term. As `(L, N)` doubles from `(2·10⁴, 500)` at `L/N = 40`, `R_0 = 7.09, 8.56, 10.86`. ~~That is about `2^{1/3}` per doubling, the growth of `(NL)^{2/3}/N`.~~ *(9.7: ungated as written.)* The factors are `1.207` and `1.269` per doubling, against `2^{1/3} = 1.260` for the growth of `(NL)^{2/3}/N`. N3 now gates them between `1.1` and `1.45`. At `(8·10⁴, 500)`, `R_0 = 17.45`.
- The twists `k = −2` (the slot coefficient's angle), `−1`, `1` and `2` give `R_k` between `0.48` and `0.75`: no excess over the diagonal.
- Controls *(added in 9.7)*: random unit phases give `R` between `0.91` and `1.01`. A coefficient aligned with one column's character gives `18.3`, `20.9`, `20.8` and `70.9` at the four sizes, at least half the aligned column's own contribution `n₀/#columns`, with `n₀` the number of moduli prime to that column: the cubic sieve's `L` term, attained. N3 gates both.

**The column term (N2).** The rows `k` are squarefree of norm `≤ K`, and the columns `n` squarefree of norm in `(N/2, N]`. Let `Q = Σ_k|Σ_n c_n(n/k)_2|²/(#rows·Σ|c_n|²)`. At `(N, K) = (8·10⁴, 250)`, `(8·10⁴, 500)` and `(4·10⁴, 1000)`:
- the aligned control `c_n = (n/k₀)_2` gives `Q = 131.2, 70.9, 21.0`, about `#columns/#rows`;
- random phases give `0.82–1.08`;
- the Gauss-sum models `conj(g₃)`, times `1`, `α`, `α²` or `μ`, give `0.59–1.02`;
- a two-slot model `conj(g₃)α·S`, built from 25 slot pairs like the release's marked slots, gives `0.99`.

The dual coefficients the models stand for come from Proposition `prop:completed-reflection`. Its "`The function $d$ is one of three fixed cusp coefficient functions.`" (line 1795), "constructed from the theta expansions in the proof" (line 1754), has support in "`\{u\lambda^k n b^3:k\ge-4,\ n,b\equiv1\pmod3,\ n\ {\rm sf}\}`" with "`|d(\mu)|\le27\,3^{k/6}|b|`" (lines 1798–1800). At squarefree `n` the models take the conjugate normalized cubic Gauss sum. That is a model of `d`, not derived here.

### 9.4 The review: findings and dispositions

The reviewer ran `slotsplit.py` (46.4 s, rc 0) and `fivesixths.py` (12.0 s, rc 0) on the four files under review. The lead verified every finding directly:
- the release's lines named (1754, 1786–1800, 1813, 1902–1910, 2258–2290, 5582–5590, 7440–7470, 7491–7499, 7505–7660, 16240–16262);
- Dunn and Radziwiłł's text (abstract, Theorems 1.3–1.4, eq. (1.13), Definition 3.1, Propositions 9.1–9.2);
- Heath-Brown's abstract;
- the two ratios papers' arXiv abstracts;
- the model, in session runs, now gated where this note relies on them.

| # | severity | finding | disposition |
|---|---|---|---|
| 1 | major | the trilinear note's character `(B/jA²)_3` is wrong; it is `conj((B/jA)_3)`, and the plain sieve gives `σ = 2/3` | accepted; struck at 7.6 and on the register; 9.1, S8 |
| 2 | minor | `σ = 1/2` also follows from `N + N^{3/4}L^{1/2}`, so the "needs" sentences overstate | accepted; markers in the Summary and sections 2, 4, 7.2, 7.6; S5 row (c) |
| 3 | minor | "square-root size" means two things, and slot sums are not products of prime sums | accepted; struck at 7.2, markers; S5 rows (a), (e) |
| 4 | minor | the ray reaches `5/6` only for `t ≥ t*` (bisected in 9.7 to `(0.557239, 0.557240)`), not for `t ≥ 1/2` | accepted; struck in the Summary and on the register, marker in section 8; S6 |
| 5 | minor | `(1, 1, 1)` is the corner of the length box and needs `μ = 2` | accepted; marker in section 8; S6 |
| 6 | minor | Čech's paper concerns real characters, and "only under GRH" is unscoped | accepted; struck at 7.1, 7.6 and on the register |
| 7 | minor | "in every source surveyed … no bound below `X^{5/6}`" overstates both sources | accepted; struck at 7.6 |
| 8 | cosmetic | register: "the follow-up below" is above | edited |
| 9 | cosmetic | S2's point `(1/4, 1/2, 1/4)` fails Xu–Sang's `11b/6` | accepted; marker at 7.3; S2 |
| 10 | cosmetic | an antecedent lost to the strike in section 2 | edited |
| 11 | cosmetic | the Summary's "no crossing" holds at `c = 1` | marker |
| 12 | cosmetic | S4(i) checks a hand-written expression | S4 now also reads the model's coefficients |
| 13 | cosmetic | S5 covered three of five rows, "never exceeds" was sampled at `ℓ′ ≤ 0.36`, and "every dual length" | marker at 7.2; table in 9.5 |
| 14 | cosmetic | section 8's settings omit round 498's readings (`0.8700000` without them) | marker in section 8; S6 |
| 15 | cosmetic | "a cost above about `0.16` buys nothing" | struck in section 8; S6 |
| 16 | cosmetic | Heath-Brown sums over integers `c ≡ 1 (mod 3)`; "(Annals 2024)" is not in the text read | edited at 7.1 |
| 17 | cosmetic | Check 4 omits S7; runtimes | edited |

Out of scope:
- O1: commits `19f70fbc` and `ffb66062` (`columnterm.py`) were not reviewed. Section 9.3 writes them up, and the next round reviews them.
- O2: `crossing.py`'s docstring and README round 500 state the dyads' maximum "In any geometry", but gate X1 samples only `ℓ′ ≤ 0.3`. At `(0.6181, 0.9935)` the program exceeds the formula by `0.178`, through a branch with `v > H`. Every low side has `M′ ≥ 2ℓ′`, because `l_x ≥ ℓ` and `b ≥ 0` give `M′ − 2ℓ′ = M − 2ℓ ≥ 0` at every tuple size. There, gate S7 now checks the formula at 300 random points. `crossing.py` gets a bracketed scope note.

### 9.5 The dictionary, corrected

| hybrid bound on `Σ_{j∼N}\|slot sum\|²` | `σ` | least low side | gates |
|---|---|---|---|
| the release's `N + L + (NL)^{2/3}` | `1` | `13/15` | F2, F3 |
| the slot split, `min(·, N L^{2/3})` (7.3) | `3/4` | `41/48` | S1, S2 |
| squared slot sums `≪ L^{1/2}` in every column (slot sums `≪ L^{1/4}`; before the `1/√q_P` normalization, `≪ L^{3/4}`), `min(·, N L^{1/2})` | `5/8` | `71/84` | S5 (a) |
| the trilinear bound, `N + (NL)^{2/3}` (9.1) | `2/3` | `28/33` | S5 (b), S8 |
| `N + N^{3/4}L^{1/2}` | `1/2` | `5/6` | S5 (c) |
| a square-root sieve, `N + (NL)^{1/2}` | `1/2` | `5/6` | S5 (d) |
| square-root cancellation in every column, `N` | `≤ 1/2` | `5/6` | S5 (e) |

Each row's program is checked at S1's points (`ℓ′ ≤ 0.36`). Only the dual lengths `N < L²` matter: for `N ≥ L²` the release's factor is already `≪ N`.

**T1, restated.** For the release's slot coefficients (9.2) and `N < L²`:

`Σ_{j∼N}|Σ_P γ₂(j; P)ᾱ(P)²ψ(P)ΠW_i/√q_P|² ≪ Z^ε(N + N^{3/4}L^{1/2})`.

That gives `σ = 1/2`. Known here: `σ = 2/3` (9.1).

### 9.6 Outcome

The goal `Re s > 5/6` is still not reached, and no new zero-free region is proved. This section adds:
- the trilinear bound, `σ = 2/3` and the least low side `28/33`, by a written argument. Alone it does not move the boundary.
- the slot coefficient as a composite Gauss sum, which states T1 inside the Kubota–Patterson family;
- the finding that Dunn and Radziwiłł's corrected sieve, as stated, ~~needs input of GRH strength here~~ does not apply here: for the slot coefficients its axiom either fails outright or asks for a zero-free region `Re s > 1/2 + η` for a fixed `L`-function of the release's family (9.7);
- the review's corrections.

Section 8's routes stand: T1 and T2 at the vertex, T3 alone across the slice for `t ≥ t*`, `t* ∈ (0.557239, 0.557240)`, and combinations of partial inputs.

Reproduce, from this directory:

```
python3 slotsplit.py                          # gates S1-S8, about 70 s
python3 columnterm.py periods_w_8e4.txt       # gates N2, N3, about 15 s; skipped without the prime data
```

### 9.7 The second review round

Same day. A fresh-context hostile reviewer read commit `88be9c78` as a convergence round. Its scope was sections 7–10 as swept, `slotsplit.py`, `columnterm.py`, the register's bullet and README round 500's struck sentence. It re-ran `slotsplit.py`, `columnterm.py`, `fivesixths.py` and `../wall78/crossing.py`, each with rc 0. It returned no major finding, four minor and eight cosmetic ones, and one out-of-scope observation. The lead checked each before accepting it:
- Dunn and Radziwiłł's Definition 3.1 and Proposition 9.1, in the PDF text of arXiv 2109.07463v3;
- the release's lines 568–575, 606–612, 3322–3332, 6866–6876 and 6904–6912;
- the preprint's `dual.tex` lines 1–60, `dispersion.tex` lines 1–120 and 416, and `angular.tex` lines 60–130;
- README rounds 454–455 (the twisted multiplicativity, `gaussP_twist`) and round 500's lines 19298–19350;
- in session runs: the conversion `γ₂(π) = (λ/π)_3 g̃(π)` at 21 primes, the ray's threshold by bisection, S5's rows at points where the branch is positive, and N3's controls. The last three are now gated.

| # | severity | finding | disposition |
|---|---|---|---|
| 1 | minor | the sweep of "In any geometry" missed the register's statement and three lines of README round 500 | accepted; struck and annotated on all four *(section 13: on three; README line 19304 was annotated, not struck, and a fifth statement, README line 18985, gets its marker in section 13)* |
| 2 | minor | 9.2 named the wrong instances of Dunn and Radziwiłł's axiom (3.2), and called it "of GRH strength" and "square-root cancellation" | accepted; struck and corrected in 9.2, the Summary, sections 5, 7.6 and 9.6, and on the register |
| 3 | minor | section 10's "Unconditionally such sums save less than any fixed power" is a universal over unconditional results | accepted; struck and scoped to the bound the preprint uses |
| 4 | minor | section 10 left out the preprint's Proposition `prop:dispersion`, which has T1's shape, with its range and its log-power saving | accepted; a bullet in section 10, markers in the Summary and on the register |
| 5 | cosmetic | the ray's threshold was rounded down under "≥": it lies in `(0.557239, 0.557240)`, and `t = 0.5572` gives `0.8333645` | edited in the Summary, sections 8, 9.4 and 9.6, and on the register; S6 bisects it |
| 6 | cosmetic | S5's "equals the branch at the optimum" could not fail, since both are `0` there | S5 checks four points where the branch is positive; marker in 7.2 |
| 7 | cosmetic | "slot sums `≪ L^{3/4}`" switched normalization | edited in the Summary, 7.2 and 9.5 |
| 8 | cosmetic | "admissible prime convolutions" passes over the slot primes' ray class and `prop:dual`'s twists | scoped in section 10 |
| 9 | cosmetic | 9.2's description of N3 left out its support | edited |
| 10 | cosmetic | `columnterm.py`: its runtime, N3's unreported skip, the ungated `2^{1/3}`, and no controls for N3 | fixed; N3 gates the growth factors and two controls; 9.3 edited |
| 11 | cosmetic | Check 4 listed as new the twisted multiplicativity the pilot already has; S8's labels | Check 4 reclassified; S8 tests the struck form `(B/jA²)_3` itself and relabels (ii) |
| 12 | cosmetic | T1's title and socket lacked net-state markers | markers in section 5 and on the register |

Out of scope, recorded (O3, process). CLAUDE.md asks that a horizon hit be recorded "the same day as a pilot README round". This branch adds no README round, to avoid a numbering clash with the main line; PR #188's description says that a round "can be assigned on merge". The hits of sections 0 and 10 are owed that round. Section 7.1's sentence on Patterson's asymptotic under GRH now has a marker pointing to section 10.

In session sabotage runs, S5 fails with row (e) held to equality, and S6 fails with the bisection started above the threshold.

The battery after the sweep, from this directory, each with rc 0: `python3 slotsplit.py` (42 s), `python3 columnterm.py periods_w_8e4.txt` (7 s), `python3 fivesixths.py periods_w_8e4.txt` (8 s) and `python3 ../wall78/crossing.py` (9 s). A container restart in between reinstalled the Python packages from `tools/requirements.txt` (numpy 2.4.6, scipy 1.17.1) and rebuilt the prime data with `periods.c`; the values of the checks whose code did not change reproduced exactly.

## 10. A horizon hit: an unconditional first moment for cubic Gauss sums

Found the same day through the release's own citation: "`The corresponding first-moment asymptotic is proved unconditionally in an independent manuscript \cite[Theorem~1.1]{OpenAICubicFirstMoment}; that result is also not used here.`" (paper.tex lines 125–128). The manuscript is OpenAI, "An unconditional first moment for cubic Gauss sums" (September 25, 2026), under `preprints/` in `github.com/openai/math`. It was read in the local mirror at commit `1581d4c`, the commit of section 0's scan. No surface of the pilot recorded it, and section 0's scan missed it.

**What it states.**
- Abstract: "We prove Patterson's first-moment conjecture for normalized cubic Gauss sums over all primary Eisenstein primes, unconditionally." Its Theorem `thm:main` is `Σ_{Nπ≤X} G(π) = (6/5)c_* X^{5/6}/log X + o(X^{5/6}/log X)`.
- Its Theorem `thm:angular`: for every fixed nonzero `ℓ`, `Σ_{Nπ≤X} θ_ℓ(π)G(π) = o_ℓ(X^{5/6}/log X)`, where `θ_ℓ(z) = (z/|z|)^ℓ`. "`The assertion is pointwise in the integer $\ell$.`"
- "In particular, no GRH-dependent cancellation result is an input." And: "We do not improve the cubic large sieve for arbitrary coefficients."
- Its Proposition `prop:dual` gives a power saving `Σ_{p,q}|A(p,q)|² ≪ Y^{7/3−η}`. It holds for character sums of "admissible prime convolutions": products of a bounded number of primes with independent smooth norm weights, every prime of norm at least `Y^c`. It holds at "the two boundary configurations of the dispersion argument", where Heath-Brown's sieve and the ordinary sieve each give `Y^{7/3}`.

**Its bearing here.**
- At one prime, the slot coefficient `γ₂(π)ᾱ(π)²` is `θ_{−2}(π)G(π)` times factors of finite order: the additive characters' normalizations and `ψ`. So `thm:angular` gives `o(X^{5/6}/log X)` unconditionally for its prime sums, up to those finite-order factors, which the theorem as stated does not include.
- That is a statement at the trivial dual, in one slot. By section 7.2 the trivial dual alone does not move the dyads' maximum, so it does not change `σ`.
- In their supports and weights, the slot products are admissible prime convolutions in the sense of `prop:dual`: each slot prime has norm `Z^{ℓ/K}`, a fixed power of the product's norm, and each slot carries its own smooth weight `W_i`. *(9.7: only in those respects. The release's slot primes lie in the ray class `1_T` (paper.tex lines 6871–6874), a restriction the definition (dual.tex lines 10–23) does not include. And `prop:dual`'s sums `A(p,q)` carry only the twists `N(b)^{iu}` and `χ_b(vpq²)` (lines 43–46), without the angle `θ_{−2}` or `ψ`.)*
- *(Added in 9.7.)* The preprint's Proposition `prop:dispersion` has T1's shape. Its `F_u(a) = Σ_b β_b(u)G(b)conj(χ_b(a))` sums products `b` that carry Gauss sums against the columns `a`, with the character `conj(χ_b(a))`, which is `χ_P(j)^{−2}`. But:
  - it is stated for "`AB\asymp X,\qquad X^{0.32}\le B\ll X^{1/2}`" (dispersion.tex line 16), that is `L ≤ N ≤ L^{2.125}` in T1's terms;
  - after its theta correction it saves only a power of `log X`: the bound is `\mathcal Q L^{-K}` (line 69), with `\mathcal Q=ABH^{1/3}` (line 17), which is `(AB)^{2/3}B`;
  - its small-conductor frequencies rest on a log-power saving, its property (SW).

  At `σ = 2/3` the second branch is maximized at a trivial dual, `N ≪ L` (F3), outside that range. The proposition would reach those dyads after the trilinear reduction of 9.1, at the balanced edge `B ≈ X^{1/2}`. So the preprint bears on T1 directly, but with a log-power saving, which does not move `σ`.
- It is open whether the preprint's corrected dispersion, applied to the angle-twisted coefficients in the mean square over the columns, saves a power on `(NL)^{2/3}`. In a corrected sieve of the shape of Dunn and Radziwiłł's eq. (1.13), the correction term for these coefficients carries sums of `β(B)θ_{−2}(B)ψ(B)N(B)^{−1/6}` over the slot products. Those are products of angular Hecke prime sums, one per slot. ~~Unconditionally such sums save less than any fixed power (the prime ideal theorem for Hecke characters), and~~ *(9.7: an unscoped universal over unconditional results.)* The unconditional bound the preprint uses for such sums, its Lemma `lem:angular-hecke`, saves a power of `log x`: "`\ll_{\ell,A,M}x(\log x)^{-M}`" (angular.tex line 77). No power saving was found in the sources read, and without one the correction term is the size of the `(NL)^{2/3}` term itself.
- Even with that settled, the remainder `(NL)^{2/3−δ}` with a small fixed `δ` would move `σ` only slightly below `2/3`, short of T1's `1/2`.

**Check 9.**
- (b) The register gets a T1 attack note: the preprint's corrected dispersion with Proposition `prop:dual`, applied to the slot coefficients. *(9.7: with `prop:dispersion`'s range and its log-power saving recorded there.)*
- (c) The signal it needs is a zero-free strip for the angular Hecke `L`-functions `L(s, θ_{−2}ψ)` over `ℚ(ω)`. These have infinite order and are outside the release's finite-order family, so the signal is auxiliary, not circular. It is also a family question in the sense of CLAUDE.md's "Families before single functions": the slot coefficients themselves generate the angular twist `θ_{−2}`. So: does the release's method, or Liu's, reach Hecke characters of nonzero infinity type?

## 11. The high side's first rung (gates H1–H6 of `highside.py`)

Same day. Sections 7–9 leave the release-level boundary at `0.8748866`, with the bins `E` binding at every `σ` (S3). This section asks what those bins need, in the release-level configuration: section 8's program at `c = 1` with Sang's rotation, round 498's readings, Xu–Sang's counts and fourth moment, and the trilinear `σ = 2/3` *(section 14: and the third Gram term soft, round 499's S3: Xu–Sang's `l_y − ℓ > 11b/6` dropped and the third term carried in the low side's maximum)*. Every number is a statement about the pilot's model. Round 498 already recorded the density-hypothesis and Lindelöf configurations at `0.8667866` with the floor bin binding, and the obstruction `13/15` (Check 4) *(section 13: on Sang's slice under his range `ℓ ≤ 1/5`, which this configuration drops)*.

**What binds (H1).** A bin is a class of Poisson rows. In Xu–Sang's notation `δ = 2a − 1`, and "`Here \(a\) records how far left the denominator contour is permitted to move on this class`" (source lines 541–542). Also `x = q/δ`, where "`Here \(q\) is the prime-length-weighted mean growth exponent of the physical prime sums, while \(x\) measures it relative to the detector parameter \(\delta\).`" (lines 904–907). The bin's endpoint, their eq. `endpoint` (lines 1335–1344), carries the count as `−(3h/4)(1 − R_κ)`.

At the optimum, the bins within `10⁻⁷` of their endpoint lie at `x = 1/2`, the largest prime amplitude, with `δ` between `0.4688` and `0.4702`. The tight low rows are the Gram bound's exceptional term and the slice.

**Relief on the bins `δ ≥ 1/8` (H2).**
- A saving `U^η` confined to `δ ∈ [0.44, 0.50]` moves the boundary only to `0.8748474`, at `η = 0.01` and `0.05` alike. Neighbouring bins take over. *(Section 13: now gated in H2. The binding bins move to `δ = 0.43997` and `0.50042`, the grid points just outside the window.)*
- On every bin `δ ≥ 1/8`, the boundary is `0.8730362` at `η = 0.01` and `0.8711404` at `0.02`, slopes of `0.185` and `0.187`. In this model, small uniform savings on those bins move the boundary in proportion. It saturates at `0.8667866` at `η = 0.045`, where the floor bin binds instead.
- Density-hypothesis counts on those bins give the same `0.8667866`, as does round 498's `counts='dh'` configuration.

**Stronger moments (H3).** The bins' numerator is bounded by Hölder with a `2k`-th moment over the rows. Xu–Sang's fourth moment is `k = 2`. ~~With `k = 5/2`, `3`, `4` and `6` the boundary is `0.8712795`, `0.8692279`, `0.8674539` and `0.8667866`. The bins `E` bind below `k = 6`, and the floor bin at `k = 6`.~~ *(Struck in section 13. The struck values keep the amplifier's share `ϑ/2` for every `k`, which README round 507 replaced beyond the fourth moment by `ϑ/k`; of its two capacity-consistent levers, `ϑ = 0` is the better at every `k` computed. With it the boundary is `0.8715666`, `0.8693505`, `0.8674755` and `0.8668665` at `k = 5/2`, `3`, `4` and `5`, with the bins `E` binding, and `0.8667866` at `k = 5.25` and `6`, with the floor bin. So "below `k = 6`" was false on `[5.25, 6)`.)* *(Section 14: the comparison is now computed and gated in H3. Sang's `ϑ` at the share `ϑ/k`, in the bins and the small bins, gives `0.8721821`, `0.8704994`, `0.8687802`, `0.8679805`, `0.8678488` and `0.8675489` at those six `k`. `ϑ = 0` now holds in the small bins too, which moves none of the gated values.)* As in rounds 497–499, the moment enters the model only through the weight `w = 1 − 1/(2k)` *(and, from section 13, with `ϑ = 0` beyond `k = 2`)*. README round 508 found that the release's method, as written, does not give a sixth moment at Sang's longest blocks.

**The next rung (H4).** With density-hypothesis counts and a saving `U^{0.001}` on the floor bin and the small bins, the boundary is `13/15` at `(2/5, 2/5, 1/5)`. `U^{0.0005}` gives `0.8667067`, with the floor bin still binding. At `13/15` the bins `E` bind together with Sang's rotation condition `h/2 < l_y`~~: round 498's obstruction~~. `σ = 1/2` changes nothing. ~~This rung is a step of only `1.2·10⁻⁴`, so after the first rung the obstruction is `13/15` itself.~~ *(Struck in section 13, false as written. Round 498's obstruction is another mechanism: the low side meets the floor bin at `ℓ = 1/5`, under Sang's range `ℓ ≤ 1/5`. And `13/15` stops only this construction, which leaves the bins `E` unsaved. With a saving on every bin, at `σ = 2/3` and with the rotation kept, the boundary goes below `13/15`, down to `41/48`, the rotation's exact floor. At the release's `σ = 1` it stays at `13/15` (H4, section 13).)* *(Section 14: exact under the program's soft third; with Xu–Sang's `l_y − ℓ > 11b/6` kept, `253/294`, H4 (iv).)*

**Where the counts come from (H5).** Xu–Sang's Proposition `prop:row-count` (arXiv 2610.15291v2, read in its source, lines 936–1078) bounds a row class by `U^{R_κ(δ,x)+ε}`. On their account, "`The exponent \(R_\kappa\) results from balancing the short simultaneous-witness estimate with the long inverse-witness estimate.`" (lines 917–919).
- The long witness uses "`The sixth-power amplification \cite[Lemma~17.6]{OAI26}`", with "`e(r)=\max\{1,(1+5r)/6\}`" (lines 451–456). Its slope `α = 5/6` enters `R_long(t) = 1 − δ + (α − δ)(t − 1)`.
- The short witnesses use the release's marked inverse moment, with capacity "`r+2z<1,\qquad 2r+8z<3.`" (line 445), and its plain fourth moment, with "`m_1+m_2+6\kappa z\le1,`" (line 473).
- Gate H5 recomputes the count with a slope `α′` in place of `5/6`, the long branch taken as `(α′ − δ)₊`. At `5/6` it reproduces the model's count and `0.8748866`. At `α′ = 3/4` the boundary is `0.8741816`, and at `1/2` it is `0.8714461`, with `E` binding. At `1/8` it is `0.8667866`, the first rung, with the floor bin binding: the count is then `1 − δ` on every bin `δ ≥ 1/8`.
- ~~The plain moment's prime capacity matters little in this count. With the constant `6` of `m₁ + m₂ + 6κz ≤ 1` replaced by `2`, the boundary is `0.8733798`.~~ *(Struck in section 13. The struck value `0.8733798` applies Xu–Sang's closed form at `c = 1/κ ≈ 1.34`, outside the range `c ≤ 6/13` of their balance. It also ignores the prime supply, which the plain selection then exceeds on 13% of the bins. The supply can only raise the count, and with the constant `6` the selections stay below the supply `1/5` that Xu–Sang's count assumes. So through the count, the constant `2` moves the boundary by at most ~~`0.0015`~~ `0.0015068` (section 14): `0.8733798 ≤ B ≤ 0.8748866` (H5). The capacity also enters the numerator's amplifier `ϑ = q/(6κ)` and the short gate, which H5 leaves unchanged.)*
- The algebra behind these: the count's excess over `1 − δ` is half of a parallel combination `ab/(a + b)` of the long branch `a = α − δ` and the short branch `b = δP_κ/D_κ` (H5 checks the identity at every bin of the grid `δ ≥ 1/8`, at the bootstrap's `κ`). So the count reaches density-hypothesis strength on a bin only where one of the two branches vanishes there. At `α′ = 1/8` the long branch vanishes on every bin `δ ≥ 1/8`.

**Survey (Check 9(a), the machinery checklist).** Searched on 2026-10-22, with abstracts read through the arXiv API:
- Guth and Maynard (arXiv 2405.20552): new large-value estimates for Dirichlet polynomials, and "`N(σ,T)\le T^{30(1-σ)/13+o(1)}`".
- Chen, Gupta and Li (arXiv 2507.08296v2): "`\sum_{χ\bmod q}N(σ,T,χ) \ll_ε (qT)^{7(1-σ)/3+ε}`", over all characters to one modulus `q`. The pilot read its Proposition 10.2 directly in README round 535, for the Linnik strand.
- Cossaboom (arXiv 2609.27715): the Guth–Maynard argument extended to `GL₂` automorphic `L`-functions, in the `t`-aspect.

None of the three abstracts treats a thin family like the release's rows: sextic characters `χ_n(u) = (u/n)_6` of the physical rows `u`. Xu–Sang's matching lower bound (section 0) shows the sextic large sieve sharp for general coefficients over the complete sextic family. This survey found no input for the first rung.

*(Added in section 13.)* Two zero-density estimates for complete families of `n`-th order characters, compared at the binding bins, where `a = (1 + δ)/2 ≈ 0.735`:
- Blomer, Goldmakher and Louvel (arXiv 1112.1650v1, read in the source; their large sieve is on the pilot's surfaces since README round 311). Their Corollary `cor:kor3` bounds `Σ*_{N𝔞≤N} N(σ, T, 𝔞)` by `N^{g(σ)}T^{1+d(1−σ)/(3−2σ)}(NT)^ε`, with "`\frac{8(1-\sigma)}{7-6\sigma}, & 1/2 <  \sigma \leq 5/6`". At `σ = 0.735` that is `g = 0.8185`.
- de Faveri's zero-density corollary (arXiv 2610.04045; on the pilot's surfaces since README round 496, `exponent_lp.de_faveri_delta`): at `n = 6` and `σ = 0.735` the count exponent `1 − δ_6(σ)` is `0.7496`.

Xu–Sang's count there (`x = 1/2`, `κ = 0.7498`) is `0.5897`, and density-hypothesis counts give `0.53`. So neither estimate improves on Xu–Sang's count at the binding bins.

The release's own Lemma `lem:inverse-amplification` (paper.tex lines 12362–12460), read for this section, gets its slope by embedding the rows `u` into the complete family through `u ↦ ua⁶`: "`The map \((u,a)\mapsto ua^6\) is injective on these pairs.`" (lines 12437–12438). Its bound `H/P = U^{1/6}H^{5/6}` already improves on the sextic large sieve's `U^{1/3}D^{5/6}` term by `U^{1/6}`. Within the lemma's method the slope is fixed: the amplifier's length `P = (H/U)^{1/6}` is set by the raw moment's range `H ≥ D^{1+c}`. On this reading a smaller slope would need a new estimate for the Möbius polynomials over this family, such as the raw moment below that range, not a different choice of `P`.

**T2, restated in two rungs** *(section 13: the second struck; what lies beyond the first rung is in section 13)*.
- First rung, to `0.8667866`. In the model each of these reaches it: density-hypothesis counts on the bins `δ ≥ 1/8` (H2), a `2k`-th moment with `k = 6` (H3), a uniform saving `U^{0.045}` there (H2), or Lemma 17.6's slope at `1/8` (H5). Through the count, it is reached when one of the count's two branches vanishes on every bin `δ ≥ 1/8`.
- ~~Second rung, to `13/15`, a step of `1.2·10⁻⁴`: a saving `U^{0.001}` among the floor bin's generic rows. Below `13/15` the rotation's condition binds (round 498).~~ *(Struck in section 13. Beyond the first rung, with density-hypothesis counts and a saving on every bin, the floor bin's generic rows included, the boundary is `0.8657615`, `0.8548781` and `41/48` at `η = 0.01`, `0.1` and `0.3`, with Sang's rotation kept (H4). `41/48` is the rotation's exact floor. ~~Below it the numerator must go unrotated:~~ (Section 14, scoped: that floor holds under the program's soft third and at crossing cost `c ≥ 1/12`; with a cheaper crossing the rotation allows `5/6 + c/4`, H8. Without the rotation:) `28/33` at `σ = 2/3`, and the vertex route at `σ ≤ 1/2`.)*
- The vertex route of sections 3–4 (no rotation, `σ ≤ 1/2`, `η ≥ 0.168`) is unchanged.

**Check 9.**
- (b) The register's T2 bullet gets these rungs, the H5 decomposition and the survey.
- (c) The signals are auxiliary. Better counts or moments for the rows' family bound polynomial moments over that family. They are not bounds equivalent to the target's zero-free half-plane, although Xu–Sang's capacities are licensed by a family zero bound `β_* ≤ (1+κ)/2`, which the bootstrap carries.

**T3's pointwise route (H6).** Bounding each `(k, P)` pair's sum over `n` by square-root cancellation forgoes the cubic sieve's average over `P`: at best it gives the factor `K·L·N·B`. At S6's first-branch dyad `(M′, ℓ′) = (2t, t)`, `t = 0.5572`, the column term's excess is `3t − 1` and the pointwise route's is `t`, ~~an effective crossing cost~~ a ratio `t/(3t − 1) = 0.8297` (gate H6, exact arithmetic)~~, against the break-even between `0.16` and `0.165`~~ *(section 14: struck, a comparison with a crossing-cost break-even, which the ratio is not)*. *(Section 13: the ratio belongs to this dyad, and at the first-branch dyad `(8/5, 1/10)` it is `1/7`, so it is not a crossing cost in the model's sense. The route's charge on the low side is at least `min(μ, ℓ)/2`: at the tuple's own first-branch dyad the pointwise excess is `ℓ`. The program charging `ℓ/2` in place of `μ/2` gives `0.9487180`, so the cheaper of the two charges leaves the boundary at `0.8748866` (H6).)* Dunn and Radziwiłł's level-aspect Voronoi formula (their Proposition 5.3) turns sums of `g̃(c)` twisted by a cubic character `(c/r)_3` into dual sums whose weight is evaluated at `N(d³ν)X/N(r)²`, a dual of length about `N(r)²/X`. T3's sums also carry the row's quadratic character, which that proposition does not include. If a formula of the same shape held for the modulus `kP`, of norm `KL`, its dual would have length `(KL)²/N = Z^{1.557}` at this dyad, longer than the rows. So the pointwise route does not reach T3 in this model.

**The coefficient models against T3 (gates N4, N5 of `columnterm.py`).** These are measurements on models at small norms, not bounds.
- N4: at N2's three sizes, the models' largest row ~~has a share `2.6–6.6` of the mean square~~ is `2.6–6.6` times `Σ|c_n|²` *(section 13; `3.99–7.74` times the mean row, now gated too)*, against `2 log(#rows) + 2 = 10.6–13.3`, and an aligned control's `5621–9974`. No single row aligns with them.
- N5: the trilinear matrix `U(k, P) = Σ_n β_n (n/k)_2 conj((n/P)_3)` bounds T3's hybrid sum by `‖U‖²_op Σ_P|c_P|²`. So a bound `‖U‖²_op ≪ Z^ε(K + L)Σ|β|²` for the release's dual coefficients would bound that sum by `Z^ε(K + L)Σ|β|²Σ_P|c_P|²`. Since `Σ|β|² ≤ N`, where `L ≤ K`, as at S6's dyad, that is the program's factor with `K + NB` replaced by `K` and the cubic sieve's factor kept: the form of T3 that S7 removes. T3 as stated in section 8, against `Σ|γ|²`, would also need a lower bound for `Σ_n|β(n)|²|S(n)|²`. At three sizes, `‖U‖²_op/(Σ|β|²(√#rows + √#moduli)²)` is `0.85–0.96` for random phases, `conj(g₃)` and `conj(g₃)α`, about what a random matrix gives, and `7.8–17.2` for an aligned control. *(Section 13: the coefficient aligned with one row's character alone, `β_n = (n/k₀)_2`, which attains ~~N2's column term (`Q = 21–41`)~~ the column term of N2's statistic at N5's sizes (`Q = 21.0–41.2`, against `#columns/(2#rows) = 10.0–20.1`; gated since section 14), has ratio `0.89–0.94`. The slot sums' cubic characters decorrelate it, so the operator form does not see that extremal coefficient. A large singular value of `U` needs `β` to correlate with a product `X(n)Y(n)`, where `X` combines the rows' quadratic characters and `Y` the moduli's cubic ones.)*

In session sabotage runs, H1, H2, H5 and H6 each fail on a planted defect: a looser tolerance for the binding bins, the window moved to `[0.30, 0.36]`, the slope constant changed to `0.8`, and the pointwise term `u` dropped. N4 and N5 fail with an aligned coefficient planted among the models. *(Section 13 lists the sabotage runs of the revised gates.)*

Reproduce, from this directory:

```
python3 highside.py                           # gates H1-H8 (H7 from section 13, H8 from section 14), about 5 s
python3 columnterm.py periods_w_8e4.txt       # gates N2-N6 (N6 from section 13), 10-30 s; skipped without the prime data
```

## 12. Horizon refresh: a Lindelöf-on-average bound for the cubic Kubota series, and ~~T1 for~~ smooth slots *(section 13: T1 only under two unchecked conditions)*

Same day, about 17:20Z. `github.com/openai/math` is still at `1581d4c` (`git ls-remote`). An arXiv API search (newest first; abstracts) for "zero-free" with "Hecke", "quasi-Riemann", "zero-free half-plane", "cubic large sieve", "sextic large sieve" and "cubic Gauss sums" found ~~four~~ items that no pilot surface records *(section 13: seven; the third review round found three more in the same listings, in the third bullet)*:
- arXiv 2610.24900 (Grobner), 2610.20058 (Visser) and 2610.26756 (Li and Liu) apply the quasi-Riemann hypothesis. None of the three abstracts claims a new zero-free half-plane.
- arXiv 2410.03048v3 (David, de Faveri, Dunn and Stucky), "Non-vanishing for cubic Hecke `L`-functions". Its abstract: "Our new approach makes crucial use of Patterson's evaluation of the Fourier coefficients of the cubic metaplectic theta function, Heath-Brown's cubic large sieve, and a Lindelöf-on-average upper bound for the second moment of cubic Dirichlet series that we establish."
- *(Added in section 13.)* arXiv 2610.20600 (Bhargava and Vemulapalli, small defining polynomials for number fields): "Our proof does not use the Quasi-Riemann Hypothesis." arXiv 2610.19597 (Banks and Shparlinski, on the Erdős–Odlyzko–Sárközy conjecture): "We also present conditional versions of these results for arbitrary `$q$` under a quasi-Riemann hypothesis." arXiv 2609.23222v2 (Fiori and Jaskari, explicit bounds for the prime number theorem), which uses "the zero-free half-plane `$\Re(s)>7/8$` announced by OpenAI in October 2026". None of the three abstracts claims a new zero-free half-plane.

None of the ~~four~~ seven *(section 13)* reaches `5/6` or claims a boundary below Liu's.

**The lemma.** It was read in the source (`main.tex`, lines 1763–1768), with `ψ(r, s) = Σ_{c ≡ 1 (3)} g₃(r, c)N(c)^{−s}` (their eqs. `psizetadef`, `psirsdef`) and `g₃(μ, c) = Σ_{d mod c} χ_c(d)ě(μd/c)` (eq. `generalgauss`). It reads: "`For any $0 \neq h \in \Z[\omega]$, $t\in \R$, $1 < \sigma \leq \frac{5}{4}$, and $M \geq 1$, we have the bound`", namely `Σ_{0 ≠ m, N(m) ≤ M} |ψ(hm, σ + it)|² ≪_{σ,ε} N(h)^{1/2}M^{1+ε}(1 + |t|)²`. The proof combines Patterson's functional equation with the cubic large sieve. Their Lemma `psi_convexity_lemma` gives `ψ(r, s)` "`at most a simple pole at $s = \frac{4}{3}$`", with residue `c₀τ₃(r)/N(r)^{1/6}`.

**Its bearing on T1.**
- `Re s = 1` is the normalization of T1's slot sums. The release's column factor `χ_P(v)²` is `(v/P)_3`, DDDS's `χ_c`. So `γ₂(j; P)/√q_P` is `g₃(j, P)/N(P)`, up to the fixed rescaling between the two additive characters.
- Take a smooth slot instead: all `c ≡ 1 (3)` of norm about `L`, weighted by `W`. Mellin inversion writes the column sum `Σ_c g₃(j, c)W(N(c)/L)/N(c)` as an integral of `ψ(j, 1 + w)L^w W̃(w)`. Move the line to `Re w = ε`; that leaves the pole at `w = 1/3` and an integral of `ψ(j, 1 + ε + it)`.
- At a squarefree column `j`, `|τ₃(j)|` is a constant (their eq. `tau_fourier_coeff_def`). So over the columns `j ∼ N`, the pole's term has mean square about `N^{2/3}L^{2/3}`: the cubic sieve's `(NL)^{2/3}` term, attained through Patterson's theta coefficients. By the lemma with `h = 1`, the integral's mean square is `≪ N^{1+ε}`.
- So for smooth untwisted slots, the column sums obey `N + (NL)^{2/3}`, with no `L` term. That is the trilinear bound's shape (`σ = 2/3`, section 9.1), and no better.
- The slot coefficient carries the angle `ᾱ²`. With that twist the pole at `4/3` is expected to vanish: the constant term would then carry a Hecke `L`-function of a Grössencharacter of nonzero infinity type, which has no pole. At primes, gate N1 and OpenAI's `thm:angular` (section 10) agree. If, in addition, the lemma extends to the angular twist and the finite-order `ψ`, then smooth angle-twisted slots give `Σ_j|column sum|² ≪ N^{1+ε}`: row (e) of the dictionary, `σ ≤ 1/2`. This note checks neither the vanishing nor the extension.
- The release's slots are products of one prime from each slot. The lemma's proof uses the Kubota series' functional equation, and sums over prime products have none. On this reading the obstruction to T1 is the prime support of the slots. That is T1's attack note 3 ("slots over squarefree or rough integers"); a different support would mean redoing the compensation and the high side's prime-factor moments. *(Section 13, gate N6: with two-prime slots `P = pq`, one prime from each of two windows, the untwisted sums keep a theta excess, `R_0 = 1.94–2.73` at small norms, and the angle `ᾱ²` removes it, `R_{−2} = 0.84–0.95` (section 14: with one inert prime in each run's windows; over split primes only, as N6 now computes, `1.84–2.71` and `0.86–0.96`), as N3 found for all squarefree `P`. N3 measures the smooth-slot model of this section, and N6 the release's product structure at two slots.)*

T1 alone does not move the boundary: the bins `E` bind at every `σ` (S3).

**Check 9.**
- (a) "None reaches `5/6`" is scoped to the ~~four~~ seven *(section 13)* abstracts, and the bearing on T1 to the reading above.
- (b) The register's T1 attack note 3 gets the lemma.
- (c) The signal is auxiliary: the lemma bounds Gauss sums, not the target's zeros.

These hits, like those of sections 0 and 10, are owed a README round at merge (9.7, O3).

## 13. The third review round, and two gates added

Same day. A fresh-context hostile reviewer read commit `930eeeea`, the second round's sweep, as a convergence round. It read commits `e292da61` and `4a1ef710` as new material: sections 11–12, `highside.py`, gates N4–N5 and the register's two new sub-bullets. It re-ran `highside.py`, `columnterm.py` and `slotsplit.py`, each with rc 0, and ran thirteen sabotage copies, each failing only the gates it targeted. It returned one major finding, five minor and seven cosmetic ones, and one out-of-scope observation. The lead checked each before accepting it:
- README round 498 (its obstruction, and gate W1 at line 19184), round 506 (line 19697), round 507 (lines 19767–19828), and the "any geometry" statements at lines 18985 and 19300–19348;
- Xu–Sang's count (arXiv 2610.15291v2 source): the prime selection (lines 963–997), the short witnesses with "For `\(c\le6/13\)`" (lines 1003–1044) and the long witnesses (lines 1045–1064);
- the arXiv abstracts of 2610.20600, 2610.19597 and 2609.23222v2;
- in session runs of the lead's own scripts, every number of findings 1–3, 5, 12 and 13 and of the out-of-scope observation. Each reproduced exactly, ~~and each is now gated~~ *(section 14: two were not gated then, the comparison of H3's two levers and N5's `Q`; both are now)*.

| # | severity | finding | disposition |
|---|---|---|---|
| 1 | major | at `σ = 2/3`, `13/15` is not an obstruction after the first rung: a saving on every bin goes below it with Sang's rotation kept; and round 498's obstruction is another mechanism (the low side meeting the floor bin at `ℓ = 1/5`) | accepted; struck in the Summary, in section 11 (H4 and the restated rungs) and on the register; H4 rewritten, below |
| 2 | minor | H3's values keep the amplifier's share `ϑ/2`, which README round 507 replaced beyond the fourth moment | accepted; struck in section 11 and on the register; H3 gates the capacity-consistent `ϑ = 0` values |
| 3 | minor | "The bins `E` bind below `k = 6`" is false on `[5.25, 6)` | accepted; struck; H3 gates `k = 5` and `5.25` |
| 4 | minor | Summary 12 and section 12's heading drop the two conditionals that T1 for smooth slots needs | accepted; struck and corrected |
| 5 | minor | H5's capacity variant applies Xu–Sang's closed form outside `c ≤ 6/13` and beyond the prime supply | accepted; struck and scoped in section 11 and on the register; H5 gates `c > 6/13`, the excess over the supply and the constant 6's fit |
| 6 | minor | section 12's census of four new items misses three in the same listings | accepted; the three added, the counts corrected in section 12 and on the register |
| 7 | cosmetic | 9.1's count `674` is stale; S8 prints `673` | edited, with what the sabotage run shows |
| 8 | cosmetic | 9.7's row 1 overstates its disposition, and README line 18985 carries a fifth "in any geometry" | marker in 9.7; README line 18985 marked |
| 9 | cosmetic | antecedents lost to strikes: the Summary's items 8 and 9, and the register | edited |
| 10 | cosmetic | Check 4: H1's binding bins refine round 498's W1; round 506 recorded a Lindelöf-on-average bound for Kubota's series; H3 depends on round 507 | reclassified |
| 11 | cosmetic | register: "moves nothing" for `0.8748474`; "matters little" without its scope | struck and corrected on the register |
| 12 | cosmetic | "effective crossing cost" names a one-dyad ratio | struck in the Summary, section 11 and on the register; H6 adds the ratio `1/7` at `(8/5, 1/10)` and the program charging `ℓ/2` |
| 13 | cosmetic | N4's "share of the mean square"; "at every bin" in H5; "Neighbouring bins take over" ungated; the runtime strings | edited; H2 and N4 gate the two claims |

Out of scope, recorded (O4): a coefficient aligned with one row's quadratic character alone passes N5. N5 now gates it as a control, and section 11's N5 bullet records what it means for T3.

**Beyond the first rung (H4, rewritten).** With density-hypothesis counts and Sang's rotation kept, at `σ = 2/3`:
- a saving `U^η` on every bin, the floor bin and the small bins included, gives `0.8657615` at `η = 0.01` and `0.8548781` at `0.1`, with the floor bin and the rotation's `h/2 < l_y` binding; at `η = 0.3` it gives `41/48`, at `(1/4, 1/2, 1/4)`, with `h/2 < l_y`, the low side and `l_x > ℓ` binding;
- with Xu–Sang's counts in place of density-hypothesis ones, `0.8550809` at `η = 0.1` and `41/48` at `0.2` (session runs, not gated);
- a saving on the floor bin and the small bins only stops at `13/15`, with the bins `E` binding: the old H4;
- at the release's `σ = 1` the boundary is `13/15` at `η = 0.01`, `0.1` and `0.3`, with the row loss binding: the low side's floor there (F2; session runs, and H4 gates `0.1`).

**The rotation's floor (H4 (iii), exact).** Under `h/2 ≤ l_y`, `ℓ ≤ l_x`, `b ≥ 0` and `M + ℓ ≤ 1` the low side satisfies

`s₀ − 5/6 ≥ (l_x − ℓ)/6 + b/12 ≥ (1 + l_x − 3ℓ)/24 ≥ 1/48`.

The Gram term is at least `b/12`, and the rotation gives `b ≥ (1 − 3l_x + ℓ)/2`. The slice and the rotation give `3ℓ ≤ 1 − l_x`, and `ℓ ≤ l_x` gives `3ℓ ≤ 3l_x`, so `1 + l_x − 3ℓ ≥ max(2l_x, 1 − 2l_x) ≥ 1/2`. Equality holds only at `(1/4, 1/2, 1/4)`, where the low side is `41/48` for every `σ ≤ 3/4`, since the row loss `(σ − 3/4)/4` is not positive there. With a crossing `μ` at cost `c` the same algebra gives `1/48 + (c/2 − 1/24)μ`, so a crossing lowers this floor only for `c < 1/12`; section 8's ray at `c = 0` is such a case (that remark is not gated). So in this model Sang's rotation stops the descent at `41/48`, not at `13/15`. The vertex route of sections 3–4 already drops the rotation, by the reading of `h < 2l_y` at `ϑ = 0`. Without the rotation, `σ = 2/3` reaches `28/33` (H4), and `5/6` still needs `σ ≤ 1/2` and the small rows' line (sections 3–4).

*(Section 14: in this model under the soft third, round 499's S3 reading, which `slotsplit.cross_cfg` sets. The unique equality point violates Xu–Sang's `l_y − ℓ > 11b/6`, since `1/4 < 11/24` there. With that condition kept the floor is `253/294 ≈ 0.8605442`, at `(16/49, 22/49, 11/49)`: H4 (iv). The crossing remark's consequence, the floor `5/6 + min(c/4, 1/48)` with the rotation, is gated since section 14, in H8.)*

**Where the counts would have to improve (H7).** Density-hypothesis counts `R = 1 − δ` on a window of bins only, in the release-level configuration:

| window of `δ` | `a = (1 + δ)/2` | boundary |
|---|---|---|
| `[4/7, 5/6]` | `[11/14, 11/12]` | `0.8748866` (unchanged) |
| `[1/8, 0.45]` | `[9/16, 0.725]` | `0.8748866` (unchanged) |
| `[0.40, 0.55]` | `[0.70, 0.775]` | `0.8746407` |
| `[0.30, 0.65]` | `[0.65, 0.825]` | `0.8735094` |
| `[0.20, 0.75]` | `[0.60, 0.875]` | `0.8712876` |
| `[1/8, 0.70]` | `[9/16, 0.85]` | `0.8706204` |
| `[1/8, 5/6]`, every bin (H2) | `[9/16, 11/12]` | `0.8667866` |

In the three windows around `0.47` the binding bins lie just outside the window, at `x = 1/2`. A saving `U^{0.05}` on `[0.40, 0.55]` gives the same value as density-hypothesis counts there. So in this model a count improvement has to cover a broad band of `δ` around the binding `0.47` to move the boundary appreciably. Counts confined to `δ ≥ 4/7`, or to `δ ≤ 0.45`, move nothing.

**Two-prime slots (N6).** N3 sums over all squarefree `P` of one norm range: the smooth-slot model of section 12. The release's slots are products of one prime per slot. N6 takes two windows `W1`, `W2` of split primes of norm in `(P0, 2P0]` *(section 14: as written, the filter also admitted one inert prime at each `P0`, `29` (norm `841`) in `W1` at `P0 = 600` and `41` (norm `1681`) in `W2` at `P0 = 1000`; the windows now hold split primes only, cut at the median norm, so that conjugate primes share a window)* and `P = pq` with `p ∈ W1`, `q ∈ W2`, with the composite Gauss sum `γ₂(pq) = (q/p)_3(p/q)_3γ₂(p)γ₂(q)` (twisted multiplicativity, S8 (ii)), against the squarefree columns `j` of norm `≤ N`:

| `P0`, windows | `N`, columns | `R_0` | `R_{−2}` | random | aligned (floor) |
|---|---|---|---|---|---|
| `600`, ~~`44 × 45`~~ `44 × 44` | `1000`, `281` | ~~`1.935`~~ `1.839` | ~~`0.913`~~ `0.946` | ~~`0.983`~~ `1.012` | ~~`7.9` (`3.5`)~~ `7.8` (`3.4`) |
| `1000`, ~~`68 × 69`~~ `68 × 68` | `1000`, `281` | ~~`2.726`~~ `2.713` | ~~`0.842`~~ `0.855` | ~~`1.057`~~ `1.000` | ~~`17.6` (`8.3`)~~ `17.4` (`8.2`) |
| `1000`, ~~`68 × 69`~~ `68 × 68` | `2500`, `700` | ~~`2.270`~~ `2.260` | ~~`0.945`~~ `0.956` | ~~`1.001`~~ `1.002` | ~~`7.7` (`3.4`)~~ `7.6` (`3.3`) |

The untwisted sums carry a theta excess, which grows with `L` at fixed `N`, and the slot coefficient's angle `k = −2` removes it, as in N3. Without the pair phase `(q/p)_3(p/q)_3` (a session sabotage run) `R_0` falls to ~~`1.50–1.71`~~ `1.50–1.69` (section 14: over split primes only) and the gate fails. These are models at small norms, not a bound.

**Horizon notes** (abstracts, arXiv API; new to the pilot). de Faveri and Pandey, arXiv 2610.01035, "The sixth moment of the Riemann zeta function", prove `∫_0^T|ζ(1/2+it)|⁶dt ≪_ε T^{5/4−1/60+ε}` from "new large value estimates for the Riemann zeta function on the critical line". That is the `t`-aspect, while the bins that bind here are in the family aspect. Hong, arXiv 2610.15316, "Non-vanishing of primitive cubic, quartic and sextic L-functions", works over `𝔽_q[T]`. Neither bears on T1–T3 as modelled.

**Sabotage runs of the revised gates** (session copies, each failing only its target gate):
- H2: the window's saving removed, so the binding bins sit inside it;
- H3: the share `ϑ/2` in place of `ϑ = 0`;
- H4: the rotation's condition dropped at `η = 0.3`; separately, the bound's `−3ℓ` changed to `−2ℓ`;
- H5: the supply set to `0.3`;
- H6: the charge `ℓ/8` in place of `ℓ/2`;
- H7: the window `[0.40, 0.56]` in place of `[0.40, 0.55]`;
- N5: the row-aligned coefficient replaced by a fully aligned one;
- N6: the angle twist removed; separately, the pair phase dropped.

**The battery after the sweep**, from this directory, each with rc 0: `python3 highside.py` (3 s), `python3 columnterm.py periods_w_8e4.txt` (13 s), `python3 slotsplit.py` (42 s), and the unchanged `python3 fivesixths.py periods_w_8e4.txt` (8 s) and `python3 ../wall78/crossing.py` (8 s).

**Check 9.**
- (a) Every number is a statement about the pilot's model of the release's exponent system. The rotation's floor is exact within the model's low side. The census is scoped to the listings searched.
- (b) The register's T2 sub-bullet is corrected with strikes and markers, and gets the rotation's floor, ~~H7 and N6~~ *(section 14: H7 and N6 went into a new sub-bullet, "The third review round", with the floor)*.
- (c) The signals are unchanged: T1, T2 and T3 are auxiliary inputs.

**Outcome.** The goal is still not reached, and no new zero-free region is proved. The corrected picture of T2 at `σ = 2/3` is:
- the first rung, `0.8667866`;
- with savings on every bin and Sang's rotation, down to the rotation's floor `41/48` *(section 14: under the soft third; `253/294` with Xu–Sang's `l_y − ℓ > 11b/6` kept)*;
- without the rotation, `28/33`.

`5/6` still needs T1 (`σ ≤ 1/2`) with T2 at the vertex (sections 3–4), or T3 across the slice (section 8).

## 14. The fourth review round, and the T1–T3 trade-off

Same day. A fresh-context hostile reviewer read commit `98e276dd`, the third round's sweep, as a convergence round, with section 13's new material. It re-ran `highside.py`, `columnterm.py` and `slotsplit.py`, each with rc 0, and ran scratch experiments of its own. It returned no major finding, three minor ones and eight cosmetic ones. The lead checked each before accepting it:
- Xu–Sang's eq. `low-geometry` (arXiv 2610.15291v2 source, line 608) and their admissibility item 1, which ends "`\(l_x>\ell\), and \(l_y-\ell>11b/6\).`" (line 1368); the release's "`l_y-d-11b/6\ge1/12.`" (paper.tex line 8597); `slotsplit.cross_cfg`, which sets `soft_third=True`;
- `composite.py`'s `InertPrime` (norm `q²`) and `load_primes`, which returns the inert primes with the split ones;
- README line 19697, "de Faveri, Dunn and Hoffstein, arXiv 2607.07911";
- in session runs, the hard-third floor `253/294`, the 31 inert primes with `γ₂ = 1` and `α = −1` at each, the inert primes `29` and `41` in N6's windows, the split-only values, and the other lever of H3. Each reproduced. The values the note now relies on are gated (H3, H4 (iv), N1, N6); the inert primes' values explain the old numbers and are not gated.

| # | severity | finding | disposition |
|---|---|---|---|
| 1 | minor | the rotation's "exact floor" `41/48` holds only under the program's soft third, which sections 8, 11 and 13 and `highside.py` never named; with Xu–Sang's `l_y − ℓ > 11b/6` kept it is `253/294` | accepted; markers in the Summary, in sections 8, 11 and 13 and on the register; the docstring names the reading; H4 (iv) gates `253/294` |
| 2 | minor | at each `P0`, one of N6's windows of "split primes" admitted an inert prime | accepted; N6 runs over split primes, cut at the median norm, with the window sizes gated; values struck and replaced in section 13, and marked in section 12 and on the register |
| 3 | minor | N1's "7827 split primes" include 31 inert primes, at which `γ₂ = 1` and `α = −1` (pre-existing, outside the diff) | accepted; N1 runs over the 7796 split primes; values struck and replaced in the Summary and in section 2, and marked on the register; N1 gates the count and the untwisted sum's log-slope |
| 4 | cosmetic | "at most `0.0015`" rounds the bound down: the width is `0.0015068` | struck and corrected in section 11 and on the register |
| 5 | cosmetic | antecedents lost to strikes in section 13's markers: the Summary's item 11, section 11's H3 and H5, and the register | edited |
| 6 | cosmetic | section 11's H6 paragraph keeps "against the break-even" | struck |
| 7 | cosmetic | Check 4 names "David–de Faveri–Dunn–Hoffstein" | struck and corrected |
| 8 | cosmetic | section 13's "each is now gated" covered two ungated claims, H3's comparison of its two levers and N5's `Q`, which section 11 labelled as N2's | struck; both gated; the label corrected |
| 9 | cosmetic | the lever `ϑ = 0` left the small bins on Sang's `ϑ` | the small bins set to `ϑ = 0` as well, in H3's runs and in H4's unrotated run; no gated value moves |
| 10 | cosmetic | "Below it the numerator must go unrotated" is unscoped | struck and scoped |
| 11 | cosmetic | section 13's Check 9 (b) puts H7 and N6 in the register's T2 sub-bullet | struck and corrected |

**The soft third (finding 1, H4 (iv)).** `slotsplit.cross_cfg` sets `soft_third=True`: Xu–Sang's `l_y − ℓ > 11b/6` is dropped, and the third Gram term is carried in the low side's maximum (round 499's S3). Section 13's floor uses the first half of eq. `low-geometry`, `l_x > ℓ`, but not the second, and its equality point `(1/4, 1/2, 1/4)` violates the second. With the second kept:
- the program at `η = 0.3` gives `253/294 = 0.8605442` at `(16/49, 22/49, 11/49)`, with `h/2 < l_y`, the slice and `l_y − ℓ > 11b/6` among the walls;
- the low side's own linear program with that row gives `253/294`, and `fivesixths.low` is `253/294` at that point.

So the rotation's floor is `41/48` under the soft third and `253/294` under Xu–Sang's condition. Both lie below `13/15`, so section 13's major correction stands.

**Inert primes (findings 2 and 3).** `composite.load_primes` returns the split primes and the inert ones, whose norms `q²` are `1 mod 3` as well, so the filter on the norm admitted both. At each inert prime `γ₂ = 1` and `α = −1`, so the 31 of norm `≤ 8·10⁴` added a coherent `±31` to every twisted sum of N1. N1 and N6 now select the split primes.
- N1, over 7796 primes: `862` at `k = 0` and `143, 122, 129, 74, 80, 65` for `k = −3, …, 3`, against `√n = 88.3`. The untwisted sum's log-slope from `2·10⁴` to `8·10⁴` is `0.78`; N1 gates it between `0.7` and `5/6`. For comparison, `X^{5/6}/log X` has slope `0.74` there and `√n` has `0.45`.
- N6's windows are cut at the median norm. They hold `44 + 44` primes at `P0 = 600` and `68 + 68` at `P0 = 1000`, gated exactly. `R_0` is `1.839`, `2.713` and `2.260`, and `R_{−2}` is `0.946`, `0.855` and `0.956`. The threshold is lowered from `R_0 ≥ 1.8` to `R_0 ≥ 1.75`, placed between the no-phase sabotage's largest value, `1.69`, and the least observed value, `1.84`.

The findings stand as before: the twist `k = −2` carries no main term at these sizes, and the angle removes the theta excess.

**H3's other lever (finding 8).** README round 507: "at a given geometry the best `ϑ` is Sang's in every bin or `0` in every bin". H3 now computes both, with the share `ϑ/k` in the bins and the small bins (the floor bin has `ϑ = 0`). Sang's `ϑ` gives `0.8721821`, `0.8704994`, `0.8687802`, `0.8679805`, `0.8678488` and `0.8675489` at `k = 5/2`, `3`, `4`, `5`, `5.25` and `6`, each above the value with `ϑ = 0`. So `ϑ = 0` is the better lever at each `k` computed, as section 13 said.

**The T1–T3 trade-off (gate H8).** Sections 7–9 named three targets: T1, `σ ≤ 1/2` (a square-root cubic large sieve for the slot coefficients); T2, savings on the high side's bins; and T3, `c = 0` (a crossing of the slice without the column term). H8 asks how partial forms of T1 and T3 combine when T2 is strong. It uses density-hypothesis counts and a saving `U^{0.2}` on every bin, and no bin binds at any of its optima.

Without the rotation (`ϑ = 0`, `h/2 < l_y` dropped, the small rows' line at `1/6 + 1/100`), the boundary is

`B(σ, c) = 5/6 + (2σ − 1)₊ · min(1/(6(4σ + 1)), c/(12c + 5 − 4σ))`.

The derivation:
- Write `u = M − 2ℓ`. With `b ≥ 0` and `l_x ≥ ℓ`, `u ≥ 0`. Section 1's identity, with the program's two branches as alternatives, gives `s₀ − 5/6 = u/12 + (Gram excess)/2 + max(cμ, L)/2`. Here `μ = (M + ℓ − 1)₊ = (3ℓ + u − 1)₊`, and the row loss is `L = (1 + (4σ − 1)ℓ − 2M)/4 = (1 − (5 − 4σ)ℓ − 2u)/4`. The Gram excess is nonnegative and vanishes at `b = 0`. So the least low side is `5/6` plus the least value of `u/12 + max(0, c(3ℓ + u − 1)/2, (1 − (5 − 4σ)ℓ − 2u)/8)` over `u, ℓ ≥ 0`.
- For `σ ≤ 1/2` that value is `0`, at `u = 0` and `ℓ ∈ [1/(5 − 4σ), 1/3]` (F2's vertex).
- For `σ > 1/2`, put `D = 12c + 5 − 4σ` and `c₀ = (5 − 4σ)/(24σ − 6)`; then:
  - If `c ≤ c₀`, the vertex `u = 0`, `ℓ = (1 + 4c)/D` gives `c(2σ − 1)/D`. It is the diagonal point where the crossing charge `c(3t − 1)/2` meets the row loss's charge `L/2 = (1 − (5 − 4σ)t)/8`. The weights `(5 − 4σ)/D` and `12c/D` on the last two terms of the maximum give the same lower bound.
  - If `c ≥ c₀`, the vertex `u = (4σ − 2)/(1 + 4σ)`, `ℓ = 1/(1 + 4σ)`, on the slice, gives F2's `(2σ − 1)/(6(4σ + 1))`. The weights `(5 − 4σ)/(6c(1 + 4σ))` and `2/(1 + 4σ)` give the same lower bound.
- In each case the weights are nonnegative and leave nonnegative coefficients on `u` and `ℓ`. In the first case they sum to `1`, and the coefficient on `u` is nonnegative exactly when `c ≤ c₀`. In the second case both coefficients vanish, and the weights sum to at most `1` exactly when `c ≥ c₀`.

H8 checks the vertices and the weights in exact arithmetic at 20 rational `(σ, c)`. It also checks the program against the law at 20 points (within `10⁻⁶`, with no bin among the walls), and the diagonal's meeting point exactly at 12 rational `(σ, c)`.

With Sang's rotation kept, section 13's algebra with a crossing gives `s₀ − 5/6 ≥ max(cμ/2, 1/48 + (c/2 − 1/24)μ)` under `h/2 ≤ l_y`, `ℓ ≤ l_x` and `b ≥ 0`. Its least value over `μ ≥ 0` is `min(c/4, 1/48)`, at every `σ`. For `σ ≤ 3/4` it is attained at `(1/2, 1/2, 1/2)` when `c ≤ 1/12`, and at `(1/4, 1/2, 1/4)` when `c ≥ 1/12`. H8 checks the bound at 4000 random rational points and the two equalities exactly. The program gives `5/6 + c/4` at `(1/2, 1/2, 1/2)` for `σ ∈ {0.55, 2/3, 3/4}` and `c ∈ {0.01, 0.06}`, with the third Gram term soft and hard alike.

**What it means.** In the model T1 moves only the second branch (its row loss), and T3 only the first (its crossing charge). The low side pays the larger of the two at one geometry, so partial forms of the two multiply: for `σ > 1/2` the excess is `2σ − 1` times a factor that vanishes only at `c = 0`. No pair with `σ > 1/2` and `c > 0` reaches `5/6`, whatever T2 supplies, since the high side can only raise the boundary. At the known `σ = 2/3`, a boundary `5/6 + ε` with `ε < 1/66` needs `c ≤ 7ε/(1 − 36ε)`, and at `c = 1` the boundary is `28/33`. So one of T1 and T3 has to be complete. With the rotation kept, T1 does not help at all: `5/6` needs `c = 0`.

**Surveys for two attack notes.**
- T1's attack note 2, a Type I/II decomposition of the slot sums. David, Dunn, Hamieh and Lin, "Quartic Gauss sums over primes and metaplectic theta functions" (arXiv 2306.11875v5, read in the source). For quartic Gauss sums over primes, their Theorem `mainthm` (lines 221–229) gives `X^{5/6+ε} + X^{3/4+ε}|ℓ|^{3/2+ε}`. Their Type-II device is the twisted multiplicativity of eq. `tm` (lines 319–323), whose phase is "`\Big(\frac{a}{b} \Big)_2`" (line 322). For quartic sums the pair phase is quadratic, so the quadratic large sieve applies, and even so "`This yields an upper bound $\ll X^{5/6+\varepsilon}$ for $A \in [X^{1/3},X^{2/3}]$.`" (lines 332–333): "the `$X^{5/6+\varepsilon}$`-bottleneck in Type-II" (line 402). The slot coefficients' pair phase `(q/p)_3(p/q)_3` is cubic (S8 (ii)), and its large sieve is Heath-Brown's, which the trilinear split of 9.1 already uses. So, as written, the device is not an input for T1.
- T2's attack note 3, a first moment of the ratios that does not assume GRH. The one-shift ratios results found over number fields, by their abstracts (arXiv API), are all conditional:
  - Čech, arXiv 2110.04409v3, real characters: "All of the results are conditional under the Generalized Riemann hypothesis."
  - Gao and Zhao, arXiv 2311.08626v3, cubic Hecke `L`-functions of prime moduli over the Eisenstein field, "using multiple Dirichlet series under the generalized Riemann hypothesis".
  - Gao and Zhao, arXiv 2402.17198v2, the quartic family over the Gaussian field, "under the generalized Riemann hypothesis".

  The unconditional result found is over function fields: Wang, arXiv 2402.01214v2, on "the Ratios Conjecture over `$\mathbb{F}_q(t)$`". GRH for the rows' family is stronger than the conclusion sought, so none of these is usable as stated, as section 9 found for the first two.

**Sabotage runs** (session copies of the scripts, each failing only its target gate):
- H3: Sang's lever at the share `ϑ/2` in place of `ϑ/k`;
- H4: the hard third replaced by the soft one; separately, the linear program's `11b/6` row removed, and its sign flipped;
- H8:
  - the law's `12c` changed to `11c`;
  - the hard-third runs replaced by soft ones;
  - the saving lowered to `U^{0.1}`, so that bins bind;
  - the diagonal's `1 + 4c` changed to `1 + 3c`;
  - the rotated value `c/4` changed to `c/5`;
  - each certificate's second weight altered;
  - the rotated floor's `1/48` changed to `1/40`, and its `c/4` to `c/5`;
  - the rotated low side raised by `10⁻⁶`;
- N1: the slope's base point moved to `7.9·10⁴`; separately, the inert primes readmitted;
- N5: the row-aligned coefficient replaced by random phases;
- N6: the pair phase dropped; separately, the inert primes readmitted.

Two planted changes do not fail H8: Sang's `ϑ` restored in the bins, or in the small bins, of its unrotated runs. The bins do not bind there, and the docstring claims nothing about `ϑ` in those runs.

**The battery after the sweep**, from this directory, each with rc 0: `python3 highside.py` (4 s), `python3 columnterm.py periods_w_8e4.txt` (12 s), `python3 fivesixths.py periods_w_8e4.txt` (8 s), and `python3 slotsplit.py` (42 s), which imports `fivesixths.py`. `../wall78/crossing.py` and the files it imports are unchanged, so it was not re-run.

**Check 9.**
- (a) Every number is a statement about the pilot's model of the release's exponent system. The law is exact for the model's low side under the stated readings. "Do not combine" is scoped to the model's two branches, with T1 acting on the second and T3 on the first. The surveys are scoped to the sources read.
- (b) The register gets a sub-bullet, "The fourth review round", with the trade-off, its socket and an attack note. The swept findings get strikes and markers there.
- (c) The signals are unchanged: T1, T2 and T3 are auxiliary inputs. The ratios results rest on GRH for their families, which is stronger than the conclusion sought.

**Outcome.** The goal is still not reached, and no new zero-free region is proved. In the model with T2 strong, `5/6` needs T1 complete (`σ ≤ 1/2`, without the rotation, with T2 at the vertex) or T3 complete (`c = 0`, section 8's ray). Partial forms of the two multiply, and do not reach it.

## Check 4 and bearing on RH

**Check 4.**
- Acknowledged:
  - the release's low side and its steps (rounds 496, 500, 503);
  - the C₀ wall and the obstruction `13/15` (rounds 498–500);
  - round 500's dyad program;
  - rounds 501–502's lower end in `ℓ`;
  - round 498's readings;
  - Xu–Sang's admissibility conditions;
  - the moment lever's limits (rounds 506–508);
  - `PAIRING.md`'s boundary formula;
  - Liu's `0.874957…` (round 471) and Sang's `0.8748867` (round 496);
  - *(9.7)* the twisted multiplicativity of the cubic Gauss sums that S8 (ii) checks, which the pilot has in `composite.py` and in README rounds 454–455 (`conj gamI 2 (ab) = (a/b)₃·conj gamI 2 (a)·conj gamI 2 (b)`).
  - *(section 11)* round 498's density-hypothesis and Lindelöf configurations at `0.8667866`, its `counts='dh'` configuration, and README round 508's finding on the sixth moment;
  - *(sections 11–12, external)* Xu–Sang's count `R_κ` (their Proposition `prop:row-count`) and the release's Lemma 17.6; David, de Faveri, Dunn and Stucky's lemma.
  - *(section 13)* README round 498's gate W1, which already places the binding bins at `δ ≈ 0.47`, `x = 1/2` (H1 refines it); README round 506's record of ~~David–de Faveri–Dunn–Hoffstein's~~ de Faveri, Dunn and Hoffstein's *(section 14)* abstract, which names "a Lindelöf-on-average upper bound for the second moment of Kubota's Dirichlet series"; README round 507's share `ϑ/k`, on which H3 now rests; Blomer–Goldmakher–Louvel's large sieve (README round 311) and de Faveri's zero-density corollary (README round 496).
  - *(section 14)* round 499's soft-third reading (its S3) and Xu–Sang's `l_y − ℓ > 11b/6` (their admissibility rows), on which H4 (iv) rests; `composite.py`'s inert primes; Čech's and Gao–Zhao's cubic ratios results, recorded since section 9; section 13's crossing remark, whose consequence H8 gates.
- New here:
  - the floor `5/6` and its identity (F1);
  - the closed form of the low side's least value in `σ` (F2);
  - the second branch's trivial dual, and its slot coefficient `γ₂ᾱ²` from the marked reflection (F3);
  - the formula without the `L` term (F3);
  - the bias measured by infinity type (N1);
  - the vertex `(1/3, 1/3, 1/3)` and the two inputs it needs (F4, F5);
  - the readings of `h < 2l_y` and of the small rows' line (F6);
  - the horizon scan's hits: Liu's 2610.26835 and the two new versions of Xu–Sang;
  - section 7: the slot-split bound (S1, S2), the dictionary between hybrid bounds and `σ`, which corrects section 2 (S5), the ladder (S3), the vertex's bins (S4), and the literature's scope for T1;
  - section 8: the crossing cost as a third lever, and the target T3 (S6, S7);
  - section 10: the horizon hit (the cubic first-moment preprint) and its scoped bearing on T1;
  - section 9: the trilinear bound `σ = 2/3` (S5 (b), S8); the slot coefficient as the composite Gauss sum `γ₂(P)`, angle-twisted (9.2; *9.7: new is this identification of the release's tuple factor; the identity S8 (ii) checks is acknowledged above*); Dunn–Radziwiłł's corrected sieve found ~~circular~~ unusable as stated (*9.7*); the dictionary's rows (c) and (e); the ray's threshold, the corner `(1, 1, 1)` and the readings' load (S6); `crossing.formula`'s region (S7); the coefficient models (N2, N3); the review's corrections.
  - section 11: ~~the binding bins (H1);~~ *(section 13: H1 refines round 498's W1, acknowledged above)* the relief on the bins and where it stops (H2); the moment ladder in the release-level configuration (H3); ~~the second rung's size (H4)~~ *(section 13: H4 rewritten)*; the count's slope and capacity, and its form as half a parallel combination (H5); ~~the pointwise route's cost for T3~~ *(section 13: the pointwise route's charge)* (H6); the coefficient models' largest row and the trilinear matrix's operator norm (N4, N5);
  - section 12: the horizon refresh's ~~four~~ items *(section 13: seven)*, and the reading of David, de Faveri, Dunn and Stucky's lemma for T1.
  - section 13: the savings below `13/15` at `σ = 2/3`, and the rotation's exact floor `41/48` (H4); the windows where density-hypothesis counts would have to hold (H7); the capacity variant's scope (H5); the pointwise route's charge in the program (H6); two-prime slots (N6); the row-aligned control for the operator form (N5); Blomer–Goldmakher–Louvel's zero-density corollary compared at the binding bins; the three census items and the two horizon notes; the review's corrections.
  - section 14: the hard-third floor `253/294` (H4 (iv)); the T1–T3 law with its vertices and weights, and the rotated floor `5/6 + min(c/4, 1/48)` with a crossing (H8); H3's second lever; the split-only values of N1 and N6, and N1's log-slope; David, Dunn, Hamieh and Lin's Type-II device read against T1; Gao–Zhao's quartic ratios result and Wang's over `𝔽_q(t)`; the review's corrections.

**Bearing on RH: none.** The note proves no zero-free region and gains no constraint on zeros. It maps what one method would need.
