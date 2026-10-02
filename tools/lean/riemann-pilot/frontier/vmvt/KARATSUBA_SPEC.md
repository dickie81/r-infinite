# I.3b: the Karatsuba iteration, paper proof to be formalised (round 197)

Notation. `I = [1,P]`, `pv(x) = (Σ xᵢ, …, Σ xᵢᵏ)`, `J_s(P) = #{(x,y) ∈ I^{2s} : pv x = pv y}`.
`p` is a prime with `k < p` and `P ≤ p^k`. `Q = ⌈P/p⌉` bounds the size of `I ∩ (a + pℤ)`.

**Good/bad.** `x ∈ I^{s+k}` is *good* if some `k` coordinates have pairwise distinct residues
mod `p`, and *bad* otherwise (its coordinates lie in at most `k−1` classes).

**Step A (split).** Write `T = J_{s+k}(P)`, `T_BB = #{(x,y) agreeing, both bad}`, and
`G = #{(u,w,u',w') : u,u' ∈ I^k distinct mod p, w,w' ∈ I^s, pv u + pv w = pv u' + pv w'}`.
Then `T ≤ 2·T_BB + 16·C(s+k,k)²·G`. The proof:
- `T ≤ 2·T(x good) + T_BB`, by swapping the roles of `x` and `y`;
- `T(x good) ≤ C(s+k,k)·A`, by permuting coordinates;
- `A ≤ √(G·T)`, by Cauchy–Schwarz;
- then either `T ≤ 2T_BB`, or `T ≤ 16 C² G`.

**Step B (Hölder over classes).** `G ≤ p^{2s−1} Σ_a G_a`, where `G_a` restricts `w, w'` to the
class `a` mod `p`. This is the pointwise bound `|Σ_a f_a|^{2s} ≤ p^{2s−1} Σ_a |f_a|^{2s}` combined
with I.1.

**Step C (conditioned count).** `G_a ≤ k!·P^k·p^{k(k−1)/2}·J_s(Q)`. The proof:
- Fibre over `(u, u')`: the `(w,w')` count is a shifted count, so at most the unshifted
  `J_s(I ∩ (a+pℤ))` (`shiftCount_le`). That equals `J_s` of an interval of length `≤ Q`, by
  translation and scaling.
- A non-empty fibre forces `Σ(uᵢ−a)^j ≡ Σ(u'ᵢ−a)^j (mod p^j)` (shift by `−a`: `agree_shift`).
- Mod `p`, Newton (`p > k`) makes the residues of `u−a` a rearrangement of those of `u'−a`:
  at most `k!` residue vectors.
- For each residue vector, Linnik gives at most `p^{k(k−1)/2}` choices of `u` (`P ≤ p^k`
  makes `u ↦ u−a mod p^k` injective).

**Step D (bad count).** `#bad ≤ C(p,k−1)·((k−1)Q)^{s+k}`, so `T_BB ≤ #bad²`.

**Recursion.** Take a prime `p ∈ [P^{1/k}, 2P^{1/k}]` (Bertrand). If
`J_s(P) ≤ C_s P^{2s − k(k+1)/2 + η_s}`, then `J_{s+k}(P) ≤ C_{s+k} P^{2(s+k) − k(k+1)/2 + η_{s+k}}`
with `η_{s+k} = max((1 − 1/k)η_s, k(k+1)/2 − 2(s+1)/k)`, starting from `η_k = k(k−1)/2`
(`J_le_diag`). The first term comes from B–C, the second from D. So `η_s → 0` as
`s → ∞`: this is Vinogradov's mean value theorem in weak classical form.

The crude bad bound (D) makes `s ~ k³/4` necessary instead of Vinogradov's `k² log k`. Through
layer II this should give a growth exponent `a` below 1 but above 2/3 (my estimate; not yet
derived), which is still strictly better than de la Vallée Poussin. Sharpening D is a later
refinement.
