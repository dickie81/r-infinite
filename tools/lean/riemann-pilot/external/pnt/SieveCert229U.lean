/-
# Round 623: the certificate of the sieve route's loss at `L = 229/100` (the unconditional exponent): `total < K`

On `SieveGrid229U.grid229U` (`U1 = ⌈(40011/100000)DEN⌉`, `U2 = ⌊(47579/100000)DEN⌋`, `n = 150`), `SieveCert.total` is
less than `K`, the form round 619's `SieveMain.linnik_route_lt` takes (the total is `0.939K`, above the `0.88K` of the
earlier landings): as round 614's `SieveCert226.lean`, `rows a b` (`SieveCertDefs.lean`) is the sum of the rows
`a ≤ i < b` of the total, the total is the sum of its 21 parts (`total_eq_rows229U`; from 2 to 72 rows each, grouped
by the kernel's work), and each part is at most its bound (`rows229U_0` … `rows229U_20`, by `decide +kernel` in the
5 files `SieveCert229UP1.lean` … `SieveCert229UP5.lean`), whose sum is less than `K` (`total_lt_229U`).

The file imports `SieveCert.lean` (for `total_eq` and `rows_eq`) and `SieveCert229UP1.lean` … `SieveCert229UP5.lean`.
-/
import SieveCert
import SieveCert229UP1
import SieveCert229UP2
import SieveCert229UP3
import SieveCert229UP4
import SieveCert229UP5

namespace SieveCert

/-- The total of a grid with `n = 150` is the sum of its 21 parts. -/
theorem total_eq_rows229U_of [Grid] (hn : n = 150) : total =
    rows 0 14 + (rows 14 20 + (rows 20 23 + (rows 23 25 + (rows 25 27 + (rows 27 29 + (rows 29 31 + (rows 31 33 +
      (rows 33 35 + (rows 35 37 + (rows 37 39 + (rows 39 42 + (rows 42 49 + (rows 49 55 + (rows 55 58 +
      (rows 58 61 + (rows 61 64 + (rows 64 67 + (rows 67 73 + (rows 73 145 + (rows 145 150)))))))))))))))))))) := by
  simp only [total_eq, rows_eq, hn, Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 0 ≤ 14) (by norm_num : 14 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 14 ≤ 20) (by norm_num : 20 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 20 ≤ 23) (by norm_num : 23 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 23 ≤ 25) (by norm_num : 25 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 25 ≤ 27) (by norm_num : 27 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 27 ≤ 29) (by norm_num : 29 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 29 ≤ 31) (by norm_num : 31 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 31 ≤ 33) (by norm_num : 33 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 33 ≤ 35) (by norm_num : 35 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 35 ≤ 37) (by norm_num : 37 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 37 ≤ 39) (by norm_num : 39 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 39 ≤ 42) (by norm_num : 42 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 42 ≤ 49) (by norm_num : 49 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 49 ≤ 55) (by norm_num : 55 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 55 ≤ 58) (by norm_num : 58 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 58 ≤ 61) (by norm_num : 61 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 61 ≤ 64) (by norm_num : 64 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 64 ≤ 67) (by norm_num : 67 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 67 ≤ 73) (by norm_num : 73 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 73 ≤ 145) (by norm_num : 145 ≤ 150)]

section

attribute [local instance] grid229U

/-- **The total on `grid229U` is the sum of its 21 parts.** -/
theorem total_eq_rows229U : total =
    rows 0 14 + (rows 14 20 + (rows 20 23 + (rows 23 25 + (rows 25 27 + (rows 27 29 + (rows 29 31 + (rows 31 33 +
      (rows 33 35 + (rows 35 37 + (rows 37 39 + (rows 39 42 + (rows 42 49 + (rows 49 55 + (rows 55 58 +
      (rows 58 61 + (rows 61 64 + (rows 64 67 + (rows 67 73 + (rows 73 145 + (rows 145 150)))))))))))))))))))) :=
  total_eq_rows229U_of rfl

/-- **The certificate on `grid229U`**: the loss's bound is less than `K`, the 21 parts checked by the kernel. -/
theorem total_lt_229U : total < K := by
  rw [total_eq_rows229U]
  have h0 := rows229U_0
  have h1 := rows229U_1
  have h2 := rows229U_2
  have h3 := rows229U_3
  have h4 := rows229U_4
  have h5 := rows229U_5
  have h6 := rows229U_6
  have h7 := rows229U_7
  have h8 := rows229U_8
  have h9 := rows229U_9
  have h10 := rows229U_10
  have h11 := rows229U_11
  have h12 := rows229U_12
  have h13 := rows229U_13
  have h14 := rows229U_14
  have h15 := rows229U_15
  have h16 := rows229U_16
  have h17 := rows229U_17
  have h18 := rows229U_18
  have h19 := rows229U_19
  have h20 := rows229U_20
  have hs :
      rows 0 14 + (rows 14 20 + (rows 20 23 + (rows 23 25 + (rows 25 27 + (rows 27 29 + (rows 29 31 + (rows 31 33 +
        (rows 33 35 + (rows 35 37 + (rows 37 39 + (rows 39 42 + (rows 42 49 + (rows 49 55 + (rows 55 58 +
        (rows 58 61 + (rows 61 64 + (rows 64 67 + (rows 67 73 + (rows 73 145 + (rows 145 150)))))))))))))))))))) ≤
      15026459309741714 + (11031574565539238 + (6327160485386492 + (4995172175031701 + (5193167923341586 +
        (5050271711197417 + (4609787955373855 + (4038443214186510 + (3583737472663864 + (3253448909898381 +
        (2863733763366406 + (3432977182177876 + (6736717874268414 + (2583447644131167 + (2467115541345301 +
        (8879629653393456 + (15471438590305548 + (21161984720060148 + (46297274741570480 + (791083449266844160 +
        (119751883107505664)))))))))))))))))))) := by
    omega
  exact lt_of_le_of_lt hs (by decide +kernel)

end

end SieveCert

#print axioms SieveCert.total_eq_rows229U
#print axioms SieveCert.total_lt_229U
