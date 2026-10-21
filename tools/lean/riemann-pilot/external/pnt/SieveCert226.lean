/-
# Round 614: the certificate of the sieve route's loss at `L = 226/100` (the Weyl-conditional exponent)

On `SieveGrid226.grid226` (`U1 = ⌈(4075/10000)DEN⌉`, `U2 = ⌊(4835/10000)DEN⌋`, `n = 200`), `SieveCert.total` is at most
`0.88K`: as round 609's `SieveCert232.lean`, `rows a b` (in `SieveCertDefs.lean` since round 618) is the sum of the rows
`a ≤ i < b` of the
total, the total is the sum of its 49 parts (`total_eq_rows226`; from 1 to 53 rows each, grouped by the kernel's
work), and each part is at most its bound (`rows226_0` … `rows226_48`, by `decide +kernel` in the 5 files
`SieveCert226P1.lean` … `SieveCert226P5.lean`), so `total_le_226`.

The file imports `SieveCert.lean` (for `total_eq` and `rows_eq`; round 618) and `SieveCert226P1.lean` …
`SieveCert226P5.lean`.
-/
import SieveCert
import SieveCert226P1
import SieveCert226P2
import SieveCert226P3
import SieveCert226P4
import SieveCert226P5

namespace SieveCert

/-- The total of a grid with `n = 200` is the sum of its 49 parts. -/
theorem total_eq_rows226_of [Grid] (hn : n = 200) : total =
    rows 0 13 + (rows 13 16 + (rows 16 18 + (rows 18 20 + (rows 20 23 + (rows 23 26 + (rows 26 28 + (rows 28 29 +
      (rows 29 30 + (rows 30 31 + (rows 31 32 + (rows 32 33 + (rows 33 34 + (rows 34 35 + (rows 35 36 +
      (rows 36 37 + (rows 37 38 + (rows 38 39 + (rows 39 40 + (rows 40 41 + (rows 41 42 + (rows 42 43 +
      (rows 43 44 + (rows 44 45 + (rows 45 46 + (rows 46 47 + (rows 47 48 + (rows 48 49 + (rows 49 50 +
      (rows 50 51 + (rows 51 53 + (rows 53 55 + (rows 55 57 + (rows 57 60 + (rows 60 64 + (rows 64 69 +
      (rows 69 73 + (rows 73 76 + (rows 76 79 + (rows 79 82 + (rows 82 85 + (rows 85 88 + (rows 88 91 +
      (rows 91 94 + (rows 94 97 + (rows 97 101 + (rows 101 108 + (rows 108 147 +
      (rows 147 200)))))))))))))))))))))))))))))))))))))))))))))))) := by
  simp only [total_eq, rows_eq, hn, Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 0 ≤ 13) (by norm_num : 13 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 13 ≤ 16) (by norm_num : 16 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 16 ≤ 18) (by norm_num : 18 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 18 ≤ 20) (by norm_num : 20 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 20 ≤ 23) (by norm_num : 23 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 23 ≤ 26) (by norm_num : 26 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 26 ≤ 28) (by norm_num : 28 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 28 ≤ 29) (by norm_num : 29 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 29 ≤ 30) (by norm_num : 30 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 30 ≤ 31) (by norm_num : 31 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 31 ≤ 32) (by norm_num : 32 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 32 ≤ 33) (by norm_num : 33 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 33 ≤ 34) (by norm_num : 34 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 34 ≤ 35) (by norm_num : 35 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 35 ≤ 36) (by norm_num : 36 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 36 ≤ 37) (by norm_num : 37 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 37 ≤ 38) (by norm_num : 38 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 38 ≤ 39) (by norm_num : 39 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 39 ≤ 40) (by norm_num : 40 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 40 ≤ 41) (by norm_num : 41 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 41 ≤ 42) (by norm_num : 42 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 42 ≤ 43) (by norm_num : 43 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 43 ≤ 44) (by norm_num : 44 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 44 ≤ 45) (by norm_num : 45 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 45 ≤ 46) (by norm_num : 46 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 46 ≤ 47) (by norm_num : 47 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 47 ≤ 48) (by norm_num : 48 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 48 ≤ 49) (by norm_num : 49 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 49 ≤ 50) (by norm_num : 50 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 50 ≤ 51) (by norm_num : 51 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 51 ≤ 53) (by norm_num : 53 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 53 ≤ 55) (by norm_num : 55 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 55 ≤ 57) (by norm_num : 57 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 57 ≤ 60) (by norm_num : 60 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 60 ≤ 64) (by norm_num : 64 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 64 ≤ 69) (by norm_num : 69 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 69 ≤ 73) (by norm_num : 73 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 73 ≤ 76) (by norm_num : 76 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 76 ≤ 79) (by norm_num : 79 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 79 ≤ 82) (by norm_num : 82 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 82 ≤ 85) (by norm_num : 85 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 85 ≤ 88) (by norm_num : 88 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 88 ≤ 91) (by norm_num : 91 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 91 ≤ 94) (by norm_num : 94 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 94 ≤ 97) (by norm_num : 97 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 97 ≤ 101) (by norm_num : 101 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 101 ≤ 108) (by norm_num : 108 ≤ 200),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 108 ≤ 147) (by norm_num : 147 ≤ 200)]

section

attribute [local instance] grid226

/-- **The total on `grid226` is the sum of its 49 parts.** -/
theorem total_eq_rows226 : total =
    rows 0 13 + (rows 13 16 + (rows 16 18 + (rows 18 20 + (rows 20 23 + (rows 23 26 + (rows 26 28 + (rows 28 29 +
      (rows 29 30 + (rows 30 31 + (rows 31 32 + (rows 32 33 + (rows 33 34 + (rows 34 35 + (rows 35 36 +
      (rows 36 37 + (rows 37 38 + (rows 38 39 + (rows 39 40 + (rows 40 41 + (rows 41 42 + (rows 42 43 +
      (rows 43 44 + (rows 44 45 + (rows 45 46 + (rows 46 47 + (rows 47 48 + (rows 48 49 + (rows 49 50 +
      (rows 50 51 + (rows 51 53 + (rows 53 55 + (rows 55 57 + (rows 57 60 + (rows 60 64 + (rows 64 69 +
      (rows 69 73 + (rows 73 76 + (rows 76 79 + (rows 79 82 + (rows 82 85 + (rows 85 88 + (rows 88 91 +
      (rows 91 94 + (rows 94 97 + (rows 97 101 + (rows 101 108 + (rows 108 147 +
      (rows 147 200)))))))))))))))))))))))))))))))))))))))))))))))) := total_eq_rows226_of rfl

/-- **The certificate on `grid226`**: the loss's bound is at most `0.88`, the 49 parts checked by the kernel. -/
theorem total_le_226 : total ≤ 88 * K / 100 := by
  rw [total_eq_rows226]
  have h0 := rows226_0
  have h1 := rows226_1
  have h2 := rows226_2
  have h3 := rows226_3
  have h4 := rows226_4
  have h5 := rows226_5
  have h6 := rows226_6
  have h7 := rows226_7
  have h8 := rows226_8
  have h9 := rows226_9
  have h10 := rows226_10
  have h11 := rows226_11
  have h12 := rows226_12
  have h13 := rows226_13
  have h14 := rows226_14
  have h15 := rows226_15
  have h16 := rows226_16
  have h17 := rows226_17
  have h18 := rows226_18
  have h19 := rows226_19
  have h20 := rows226_20
  have h21 := rows226_21
  have h22 := rows226_22
  have h23 := rows226_23
  have h24 := rows226_24
  have h25 := rows226_25
  have h26 := rows226_26
  have h27 := rows226_27
  have h28 := rows226_28
  have h29 := rows226_29
  have h30 := rows226_30
  have h31 := rows226_31
  have h32 := rows226_32
  have h33 := rows226_33
  have h34 := rows226_34
  have h35 := rows226_35
  have h36 := rows226_36
  have h37 := rows226_37
  have h38 := rows226_38
  have h39 := rows226_39
  have h40 := rows226_40
  have h41 := rows226_41
  have h42 := rows226_42
  have h43 := rows226_43
  have h44 := rows226_44
  have h45 := rows226_45
  have h46 := rows226_46
  have h47 := rows226_47
  have h48 := rows226_48
  have hs :
      rows 0 13 + (rows 13 16 + (rows 16 18 + (rows 18 20 + (rows 20 23 + (rows 23 26 + (rows 26 28 + (rows 28 29 +
        (rows 29 30 + (rows 30 31 + (rows 31 32 + (rows 32 33 + (rows 33 34 + (rows 34 35 + (rows 35 36 +
        (rows 36 37 + (rows 37 38 + (rows 38 39 + (rows 39 40 + (rows 40 41 + (rows 41 42 + (rows 42 43 +
        (rows 43 44 + (rows 44 45 + (rows 45 46 + (rows 46 47 + (rows 47 48 + (rows 48 49 + (rows 49 50 +
        (rows 50 51 + (rows 51 53 + (rows 53 55 + (rows 55 57 + (rows 57 60 + (rows 60 64 + (rows 64 69 +
        (rows 69 73 + (rows 73 76 + (rows 76 79 + (rows 79 82 + (rows 82 85 + (rows 85 88 + (rows 88 91 +
        (rows 91 94 + (rows 94 97 + (rows 97 101 + (rows 101 108 + (rows 108 147 +
        (rows 147 200)))))))))))))))))))))))))))))))))))))))))))))))) ≤
      5021472774744892 + (4151819246414472 + (3270975673645792 + (3275654964694850 + (4392311959989472 +
        (3680148386702704 + (2415501076969146 + (1325023193683227 + (1412625082590074 + (1494901429958792 +
        (1559129071124296 + (1616611958447808 + (1655361389976004 + (1684342531840116 + (1692431074721515 +
        (1690794303084396 + (1667812148299010 + (1636637693185937 + (1586934696261992 + (1530521885202004 +
        (1459370738768087 + (1388572076622054 + (1313541583867575 + (1251648258243193 + (1191257375779868 +
        (1138421699003557 + (1076912458288148 + (1021440988597632 + (957798384819106 + (902140571728823 +
        (1635576218293912 + (1454924343663296 + (1342158660848329 + (5516129235103841 + (9948038581540766 +
        (7588977206375305 + (2455340857252499 + (605929020614214 + (990635694135351 + (4258264962750197 +
        (7738434492368668 + (10409612259189026 + (10998480726351280 + (11470796405456018 + (11912659504398184 +
        (16516014093535422 + (34136467041313808 + (466745278747737984 +
        (314340118065623424)))))))))))))))))))))))))))))))))))))))))))))))) := by
    omega
  exact hs.trans (by decide +kernel)

end

end SieveCert

#print axioms SieveCert.total_eq_rows226
#print axioms SieveCert.total_le_226
