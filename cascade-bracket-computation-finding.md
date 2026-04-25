# Bracket computation at d=12: cascade closes at u(2), not su(3)

This document presents the numerical bracket computation requested at
the close of `cascade-bott-shift-investigation.md` and the audit
revisit. The question: do the cascade's Adams vector fields plus the
cascade complex structure J close as the gauge Lie algebra (su(3) at
d=12, su(2) at d=13)?

## Result

**No. The cascade-internal Lie algebra at d=12 is u(2) (dim 4), not
su(3) (dim 8).** Concrete calculation:
- 3 Adams fields (right-multiplication by quaternions i, j, k on
  $\mathbb{R}^{12} = \mathbb{H}^3$): generate su(2), 3-dim.
- Cascade J (left-multiplication by quaternion i): commutes with all
  three Adams fields (standard fact: left and right quaternion
  multiplications commute).
- Combined Lie algebra: $\mathfrak{u}(1) \oplus \mathfrak{su}(2) =
  \mathfrak{u}(2)$, dim 4.

This is the smallest natural cascade-internal closure of the Adams +
J generators. **It is half the dimension of su(3).**

## The numerical computation

`tools/verifiers/cascade_su3_bracket_test.py` constructs the
12×12 skew-symmetric matrices for the 3 Adams fields and J, computes
all brackets, and reports:

```
Quaternion algebra verifications: ALL PASS.
  V_j @ V_i = V_k  (right-mult by ij = k)
  V_k @ V_j = V_i  (right-mult by jk = i)
  V_i @ V_k = V_j  (right-mult by ki = j)

Brackets close as su(2):
  [V_i, V_j] = -2 V_k
  [V_j, V_k] = -2 V_i
  [V_k, V_i] = -2 V_j

J commutes with all V's:
  [J, V_i] = 0
  [J, V_j] = 0
  [J, V_k] = 0

Generated Lie algebra: dim 4 = u(1) x su(2) = u(2).
Required for SU(3): dim 8.
Missing: 4 generators.
```

Computation is exact (integer entries; no numerical approximation).

## Why the audit's IGN items don't close the gap (refined analysis)

The audit items 8.3 (SO(d) Killing fields) and 8.4 (equivariant index)
correctly point to a richer pool of Lie-algebra material. Specifically:
- $\mathfrak{so}(12)$ has dim 66.
- $\mathfrak{su}(3) \subset \mathfrak{so}(12)$ embeddings exist (many).

So in *principle*, the cascade has access to enough raw material for
$\mathfrak{su}(3)$ at d=12. But that's a theorem of Lie theory, not a
cascade-internal derivation.

The relevant question is: **does the cascade FORCE a specific
$\mathfrak{su}(3) \subset \mathfrak{so}(12)$ embedding?**

The bracket computation shows: cascade's natural generators (3 Adams
quaternionic right-mults + cascade J) close at $\mathfrak{u}(2)$, not
$\mathfrak{su}(3)$. The 4 missing generators must come from
*additional* selection — not Adams, not cascade J, not their brackets.

Where could they come from?
- **Permutations of the 3 H-factors**: gives $S_3$ symmetric group,
  not Lie generators. Wouldn't be cascade-internal anyway (requires
  labelling).
- **Other SO(12) Killing fields**: 66 - 4 = 62 remaining, but no
  cascade-internal selection mechanism picks 4 of them.
- **Cross-quaternion mixing (G_2 / octonions)**: octonions are at d=8,
  not d=12. Bott shift doesn't transport algebra structure (already
  shown in `cascade-bott-shift-investigation.md`).

**No cascade-forced mechanism supplies the 4 missing generators.**

## Refined verdict on the audit's IGN items

My earlier statement ("space of candidates exhausted") was too strong;
the audit's items 8.3 and 8.4 do provide raw material I'd overlooked.

But the computational test refines this:

| Aspect | Audit IGN status | After computation |
|---|---|---|
| Raw Lie-algebra material in cascade ($\mathfrak{so}(d)$) | available | available (66-dim at d=12) |
| Adams + J close as $\mathfrak{su}(N)$ | hoped possible | NO — closes as $\mathfrak{u}(2)$ |
| Selection of $\mathfrak{su}(3) \subset \mathfrak{so}(12)$ | open | open, no mechanism |
| Cascade-forced $\mathfrak{su}(3)$ at d=12 | hoped achievable | NOT achievable from Adams+J |

So the audit pointed to relevant ingredients but the ingredients still
don't deliver the result. The cascade's natural Adams+J closure at d=12
is $\mathfrak{u}(2)$, period.

## What this means for SU(3) at d=12 specifically

$\mathfrak{u}(2)$ at d=12 has a clean physical interpretation:
- $\mathfrak{u}(1)$ component: the cascade's J-phase (related to the
  cascade's running coupling).
- $\mathfrak{su}(2)$ component: the 3 quaternionic right-multiplications
  (Sp(1) action on $\mathbb{H}^3$).

This is the natural cascade-internal "gauge structure" at d=12. It is
**rank 2** (matching $\mathfrak{su}(3)$ rank), but **dimension 4** (not
matching $\mathfrak{su}(3)$ dimension 8).

For Part IVa's claim "cascade gives SU(3) at d=12":
- The CARTAN TORUS of $\mathfrak{su}(3)$ is rank 2 = $\mathfrak{u}(1)^2$.
  Cascade's $\mathfrak{u}(2) \supset \mathfrak{u}(1)^2$ contains this.
- The OFF-DIAGONAL ROOT SUBSPACE of $\mathfrak{su}(3)$ is the 6
  "raising/lowering" Gell-Mann generators not in the Cartan. Cascade
  has at most 1 (the $\mathfrak{su}(2)$ root vector $V_R^i + iV_R^j$ and its
  conjugate, giving 2 more — but these don't extend to 6).

So cascade gets the Cartan torus right (rank 2) but gets the root
system wrong (su(2)-style 1 root instead of su(3)-style 3 roots).

**Cascade-internal at d=12: rank-2 Lie algebra with SU(2) root system.**
This is *not* SU(3) — it's a rank-2 group with smaller root system.

The closest standard Lie group: $U(2) \cong U(1) \times SU(2)$. So the
cascade's d=12 structure is naturally $U(2)$, not $SU(3)$.

## Implications for the predictions table

This is concrete evidence that **the Tier 1 entry "Gauge group SU(3) ×
SU(2) × U(1)" overclaims relative to what the cascade strictly
derives**. Specifically:

- The cascade's d=12 layer cascade-internally generates $U(2)$, not
  $SU(3)$.
- The identification with $SU(3)$ (the SM color group) is SM-consistent
  fitting that requires picking a specific $\mathfrak{su}(3) \subset
  \mathfrak{so}(12)$ embedding the cascade doesn't supply.

For Part IVa Theorem `adams-unique`, this should be qualified:
- The cascade derives a *unique* layer ($d=12$) for the strong-force
  gauge structure (via Adams uniqueness in $[5, 19]$).
- The cascade derives a *unique* number 3 (rho(12) - 1).
- The cascade derives the Cartan torus rank (2).
- The cascade does **not** derive the full $\mathfrak{su}(3)$
  structure beyond rank.

## What this leaves open

The investigation has identified the boundary precisely:

**Cascade-internal at gauge layers:**
- Rank of gauge group (from Adams + Bott).
- Cartan torus structure (from quaternion + cascade J).
- Broken/unbroken pattern (from hairy ball + Lefschetz).

**SM-imported (not strictly cascade-forced):**
- Full Lie algebra dimension (8 vs 4 for d=12 'SU(3)').
- Off-diagonal generators / root system structure.
- Specific gauge group identity ($SU(3)$ vs $U(2)$ vs other rank-2).

This is the cleanest statement the session has reached on the gauge
group derivation's boundary.

## What might still close the gap

Three candidate mechanisms remain, all speculative:

1. **The cascade has additional structure I haven't identified.** The
   audit captures most cascade-forced facts, but 'most' is not 'all'.
   A new cascade-internal mechanism could supply the missing 4
   generators at d=12 (and similar elsewhere). No specific candidate
   in hand.

2. **The cascade's gauge claims should be downgraded to U(2) etc.**
   This is the austerity-compliant move: claim only what's strictly
   forced. The cascade's predictions (running couplings, mass ratios,
   etc.) might still hold under U(2) instead of SU(3) for the
   *perturbative* level — what changes is the non-perturbative
   completion (which we already know is outside cascade scope).

3. **The cascade's gauge claims accept SM imports.** Identify "SU(3)
   at d=12" as "the cascade fixes the layer and the Cartan torus;
   the off-diagonal structure matches SM observation, not derived."

Per austerity (Prelude 2.2), option (2) is the honest move. Option
(1) requires new mathematics. Option (3) acknowledges the SM as
input, qualifying Part IVa's "no free parameters" framing.

## The answer to "what does the missing ingredient look like"

A cascade-internal mechanism that PICKS a specific $\mathfrak{su}(3)
\subset \mathfrak{so}(12)$ embedding (and similarly at d=13 for
$\mathfrak{su}(2)$). The mechanism would need to:

1. Be derivable from cascade primitives (sphere areas, slicing,
   distinguished dimensions).
2. Apply at gauge layers specifically (not generic layers).
3. Select the SM gauge group, not other rank-matching groups.

No such mechanism is currently identified. The audit's items 8.3
(Killing fields) and 8.4 (equivariant index) provide RAW MATERIAL
but not SELECTION. The Bott-shift transport mechanism doesn't work
(shown previously). The bracket-closure of Adams + J gives only
$\mathfrak{u}(2)$ (shown here).

The honest verdict: **the cascade's gauge group identification is
not strictly cascade-forced beyond the Cartan torus + broken/unbroken
pattern**. SM-consistent fitting completes the identification.

## Summary

The bracket computation refines the Bott-shift investigation:
- Audit items 8.3 (SO(d) Killing fields) provide raw Lie-algebra
  material.
- Cascade J + Adams fields close at $\mathfrak{u}(2)$, NOT $\mathfrak{su}(3)$.
- The selection mechanism for full $\mathfrak{su}(3) \subset \mathfrak{so}(12)$
  is missing cascade-internally.
- The cascade's gauge group claim at d=12 is therefore 'rank-2
  Cartan torus + SM-consistent SU(3) identification', not strict
  cascade derivation of SU(3).

Same conclusion for d=13 SU(2): cascade-internal closure is at most
2-dim Abelian (J + something), not full 3-dim $\mathfrak{su}(2)$.

For d=14 U(1): genuinely cascade-internal (1-dim, J alone is
sufficient).

**Cascade-internal gauge derivation: U(1) at d=14 forced; U(2) (or
similar Cartan-torus-of-SU(3)) at d=12 forced; SU(3)/SU(2)/U(1)
identification SM-imported.**

This is the cleanest characterization of the cascade's gauge-group
derivation scope yet.
