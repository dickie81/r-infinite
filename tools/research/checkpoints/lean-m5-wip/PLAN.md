# M5/M8 plan (scratch; the lead's working notes) — updated after Proposition 6 (HEAD f61aaa6)

Window: the certificate's grid window u1 = U1/DEN > 0.401, u2 = U2/DEN < 0.485 (SieveCert.u1/u2). x = q^L, L = 2.333.
z₀ = ⌈x^v⌉₊ (v = V/DEN = u2 − u1), X' = ⌊x^R⌋₊ (R = 1 − u2). As exponents of q: a₀ = Lv, b₀ = LR.
Prop 6's conditions a₀ + b₀ < 0.599L ⟺ u1 > 0.401; b₀ > 0.515L ⟺ u2 < 0.485; b₀ < L − 1 ⟺ u2 > 1/L.

## Done in scratch (r600/m5), all sorry-free, no warnings, axioms standard
Compile: `bash $S/r597/lc.sh $S/r600/m5 <Mod>` (order: SieveBrun SieveCount SieveRanges SieveLeaf SieveTree SieveDyadic
SieveTypeIIU SieveRoughTuple SieveTypeIIR SieveDiff SieveStops1 SieveCmp SieveStops2 SieveProp6 SieveChain).
- SieveBrun, SieveCount, SieveRanges, SieveLeaf: Brun's fundamental lemma in product form; leaf_A, leaf_B, leaf_gap.
- SieveTree: rough, S, primesIco, tree_pt, tree_sum. SieveDiff: tree_weighted, sum_dw_eq, leaf_diff.
- SieveDyadic, SieveTypeIIU (typeII_unw), SieveRoughTuple, SieveTypeIIR (typeII_rough).
- SieveStops1: sum_cofactor, minFac_W etc., stops1_bound, window_bound (case 1 / window; NOT used by Prop 6 now).
- SieveCmp: Cmp structure (c(m) + Σ e_i log x_i, pivot ±1, |e| ≤ 1), gt/ge/lt/prodLe/prodGt/rough/rangeLo/rangeHi/lift.
- SieveStops2: desc (Finset ↔ decreasing tuple), app (r, y, p) layout, liftc, cmps (stop comparisons), cmps_iff,
  block_strictAnti, RT (tuples by Ω), sum_stops_eq (bijection), typeII_cmp (typeII_unw for a Cmp list),
  sum_cofactor_window, cmps_length, cmps_c_le, stops2_bound (the stops at threshold X').
- SieveProp6: sum_choose_le, card_T_le, rem_le, Jw/Jw_spec, zeta, count_le_psi, leaf_bound, sum_leaves_inv,
  sum_RT_inv_le, leaves_sum_le, exists_k, window_lo, window_hi, main_coef, main_term, rem_term, **prop6**.
  DESIGN CHANGE vs SIEVE-ROUTE §5: ONE tree at threshold X' = ⌊x^R⌋ for every r ≤ x^R (no case 1/case 2 split):
  stops W ∈ (X', X'z₀] always fall in the upper window, cofactor k in (x^{u1}, 2x^{u2}); leaves d ≤ X'.

prop6 (j J₀) (Λ₁ a₀ b₀) (hab : a₀ + b₀ < 0.599L) (hb₁ : 0.515L < b₀) (hb₂ : b₀ < L − 1) (η > 0):
  ∃ δ q₀, ∀ q ≥ q₀, a unit, Ω : List (Cmp j) (len ≤ J₀, C.c 0 ≤ Λ₁ log q, prime tuples in Ω have rt_i ≥ ⌈q^{a₀}⌉ and
  ∏ ≤ ⌊q^{b₀}⌋): ‖Σ_{rt ∈ RT j N₂ Ω} Σ_n dw(n)[∏rt ∣ n ∧ rough ⌈q^{a₀}⌉ n]‖ ≤ η q^L/(φ log q) + φ⁻¹q^{L−δ}.

## M8a done (SieveChain, scratch; axioms standard)
- GCmp (coefficients in {−1,0,1}, no pivot), typeII_gcmp / typeII_gcmp' (all-zero comparisons move into m's filter).
- RTg k Y Ω (prime k-tuples ≤ Y satisfying Ω at m = 0); Split (eS, merge, factS); Transform (fullOf, splitS, liftChain);
  TLcmps (yPairs, yLast, fullTL, cmpsTL, Mset); sum_TL_eq; cmpsTL_c_le; sum_mult_eq; sum_rough_tuples.
- chainTU_bound: chains rt (entries ≥ q^{e₀}, last least, W₀ < ∏rt ≤ W₁), cofactor in the upper window.
- chainTL_bound: decreasing chains with P₁ < ∏_{i∈S} rt_i ≤ P₂ in the lower window (q^{0.401L} ≤ P₁, P₂ ≤ q^{0.485L}).
  Both: ‖Σ_rt Σ_{n∈(N₁,N₂]} dw(n)[∏rt ∣ n ∧ rough(rt last) n]‖ ≤ φ⁻¹ q^{L−δ}.

## M8 design (tasks #411–#413)
Decomposition (per n, weights f): S(A,z_top) = S(A,z₀) − Σ_{p₁} S(A_{p₁},p₁); depth 1 non-evaluable → decomposed;
depth 2 (+): evaluable / decomposed (dec cells; sum_le_of_allowed gives α₁+α₂ ≤ R) / dropped (cand ∧ ¬dec → share2;
outside cand cells → ¬hreg → only n = p₁p₂ (corner), o(x/log x) by π(√2x)²);
depth 3 (−): evaluable / decomposed (cover3 with hreg; ¬hreg ⇒ term 0 since α₁+α₂+α₃ ≤ R+R/2 < 1);
depth 4 (+): evaluable / dropped (cover4; hreg automatic) → share4.
S_f(m, z) := Σ_n f(n)[m ∣ n ∧ rough z n]; chains p₁ > ⋯ > p_k with p_k = minFac(n).

Evaluable families — which subsets S matter (geometry, for large x):
- lower window (Σ_S α ∈ (u1,u2)): any S ∋ k (newest index); TL: m = ∏_S p (squarefree), prime variables =
  (non-S chain primes) ++ (m'-tuple, non-increasing, ≥ p_k); comparisons via c(m) = log of m's sorted factors.
- upper window (Σ_S α ∈ (1−u2,1−u1)): only S = I (whole chain) is possible in the decomposition's regions
  (depth 1: α₁ < 1/2+; depth 2: α₂ < 1/2+; depth ≥ 3: parent sum ≤ R and α_k < α_{k−1}); TU: m = m' (rough
  cofactor) ∈ window, prime variables = the chain (like stops2 without the tree).
- Disjointness: classification indicators as signed sums of comparison boxes (1 − [box], inclusion–exclusion over
  events E_T = [σ_T + α_k ∈ U-part]); each box with an event → TL/TU; boxes whose only event is an impossible
  upper event are empty (linarith from parent constraints).
- Dropped B-shares: count_le_psi gives S(B_d, w) ≤ Ψ(x/d, w); share2_of_cand / share4_of_counted4 over cells;
  SieveCert.total_div_le ≤ 0.88.
- S(B, z_top)/φ ≥ (1 − o(1)) x/(φ log x): primes in (x, 2x] minus those dividing q (stack PNT, theta_near).
- Final: S(A, z_top) > 0 for large q; z_top = ⌊√N₂⌋ + 1 so z_top-rough n ∈ (N₁,N₂] is prime.

## Save points
Scratch is ephemeral: copy r600/m5/*.lean + PLAN.md to tools/research/checkpoints/lean-m5-wip/ and push
("compute checkpoint (...)", no review obligations per CLAUDE.md "Save points"); remove at landing.
