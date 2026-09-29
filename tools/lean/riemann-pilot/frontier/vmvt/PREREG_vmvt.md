# Pre-registration: Vinogradov mean values J_{s,k}(N) (round 194)

Written before running `kvmvt.py`.

J_{s,k}(N) = #{(x, y) ∈ [1,N]^{2s} : Σ x_i^j = Σ y_i^j for j = 1..k}.

Predictions:
- P1 (exact, s ≤ k): J_{s,k}(N) equals the number of pairs with y a rearrangement of x
  (Newton/Vieta). Any mismatch falsifies the Lean target `J_eq_perm`.
- P2 (bounds): N^s ≤ J ≤ N^{2s} always.
- P3 (main conjecture, now the Bourgain–Demeter–Guth / Wooley theorem):
  J_{s,k}(N) ≤ C·N^ε·(N^s + N^{2s − k(k+1)/2}). Expect the ratio
  J / (N^s + N^{2s−k(k+1)/2}) to stay O(1) up to slow (log-type) growth as N grows,
  for (k,s) ∈ {(2,3),(2,4),(3,4),(3,5),(3,6)}.
  This is a sanity check at small N, not evidence for the theorem.
