/-
# Round 631: the certificate of the sieve route's loss at `L = 2285/1000` (with no hypothesis): `total < K`

On `SieveGrid2285U.grid2285U` (`U1 = ⌈(40302/100000)DEN⌉`, `U2 = ⌊(47464/100000)DEN⌋`, `n = 250`), `SieveCert.total` is
less than `K`, the form round 619's `SieveMain.linnik_route_lt` takes (the total is below `0.98834K`): the total
is `rows 0 n` (`SieveCertCols.total_eq_rows_full`), and its bound is assembled one step at a time from the 252
parts' bounds (`rows2285U_0` … `rows2285U_251`, each by `decide +kernel` in one of the 28 part files): a heavy
row's bound from its column pieces' (`rowsJ_le_of_split`, `rows_le_of_rowsJ`; `rowsJ`, `SieveCertColsDefs.lean`),
then the 106 ranges of rows from the last to the first (`rows_le_of_split`), every bound a literal and every step a
theorem of its own (`c2285_…`, `hr2285_…`, `t2285_…`); the bounds, `⌈1.001 × part⌉` computed exactly in integers, sum to
`1140606971340984424`, less than `K` by `decide +kernel` (`total_lt_2285U`).

The file imports `SieveCertCols.lean` and `SieveCert2285UP1.lean` … `SieveCert2285UP28.lean`.
-/
import SieveCertCols
import SieveCert2285UP1
import SieveCert2285UP2
import SieveCert2285UP3
import SieveCert2285UP4
import SieveCert2285UP5
import SieveCert2285UP6
import SieveCert2285UP7
import SieveCert2285UP8
import SieveCert2285UP9
import SieveCert2285UP10
import SieveCert2285UP11
import SieveCert2285UP12
import SieveCert2285UP13
import SieveCert2285UP14
import SieveCert2285UP15
import SieveCert2285UP16
import SieveCert2285UP17
import SieveCert2285UP18
import SieveCert2285UP19
import SieveCert2285UP20
import SieveCert2285UP21
import SieveCert2285UP22
import SieveCert2285UP23
import SieveCert2285UP24
import SieveCert2285UP25
import SieveCert2285UP26
import SieveCert2285UP27
import SieveCert2285UP28

namespace SieveCert

section

attribute [local instance] grid2285U

/-! The chain of bounds: `c2285_{i}_{m}` for the heavy row `i` from its `m`-th column piece on, `hr2285_{i}` for
the heavy row `i`, `t2285_{m}` for the rows from the `m`-th range on; each a theorem of its own, its name distinct
from round 625's chain in the same namespace. -/

theorem c2285_35_0 : rowsJ 35 36 0 250 ≤ 1651815745042232 :=
  rowsJ_le_of_split 35 36 (by norm_num) (by norm_num) rows2285U_12 rows2285U_13 (by norm_num)

theorem hr2285_35 : rows 35 36 ≤ 1651815745042232 := rows_le_of_rowsJ 35 36 c2285_35_0

theorem c2285_36_0 : rowsJ 36 37 0 250 ≤ 1693889873570322 :=
  rowsJ_le_of_split 36 37 (by norm_num) (by norm_num) rows2285U_14 rows2285U_15 (by norm_num)

theorem hr2285_36 : rows 36 37 ≤ 1693889873570322 := rows_le_of_rowsJ 36 37 c2285_36_0

theorem c2285_37_0 : rowsJ 37 38 0 250 ≤ 1749403831943512 :=
  rowsJ_le_of_split 37 38 (by norm_num) (by norm_num) rows2285U_16 rows2285U_17 (by norm_num)

theorem hr2285_37 : rows 37 38 ≤ 1749403831943512 := rows_le_of_rowsJ 37 38 c2285_37_0

theorem c2285_38_0 : rowsJ 38 39 0 250 ≤ 1793183839936271 :=
  rowsJ_le_of_split 38 39 (by norm_num) (by norm_num) rows2285U_18 rows2285U_19 (by norm_num)

theorem hr2285_38 : rows 38 39 ≤ 1793183839936271 := rows_le_of_rowsJ 38 39 c2285_38_0

theorem c2285_39_0 : rowsJ 39 40 0 250 ≤ 1832359289561739 :=
  rowsJ_le_of_split 39 40 (by norm_num) (by norm_num) rows2285U_20 rows2285U_21 (by norm_num)

theorem hr2285_39 : rows 39 40 ≤ 1832359289561739 := rows_le_of_rowsJ 39 40 c2285_39_0

theorem c2285_40_0 : rowsJ 40 41 0 250 ≤ 1859490211768416 :=
  rowsJ_le_of_split 40 41 (by norm_num) (by norm_num) rows2285U_22 rows2285U_23 (by norm_num)

theorem hr2285_40 : rows 40 41 ≤ 1859490211768416 := rows_le_of_rowsJ 40 41 c2285_40_0

theorem c2285_41_0 : rowsJ 41 42 0 250 ≤ 1881349260111972 :=
  rowsJ_le_of_split 41 42 (by norm_num) (by norm_num) rows2285U_24 rows2285U_25 (by norm_num)

theorem hr2285_41 : rows 41 42 ≤ 1881349260111972 := rows_le_of_rowsJ 41 42 c2285_41_0

theorem c2285_42_0 : rowsJ 42 43 0 250 ≤ 1890536128333822 :=
  rowsJ_le_of_split 42 43 (by norm_num) (by norm_num) rows2285U_26 rows2285U_27 (by norm_num)

theorem hr2285_42 : rows 42 43 ≤ 1890536128333822 := rows_le_of_rowsJ 42 43 c2285_42_0

theorem c2285_43_0 : rowsJ 43 44 0 250 ≤ 1895245906429257 :=
  rowsJ_le_of_split 43 44 (by norm_num) (by norm_num) rows2285U_28 rows2285U_29 (by norm_num)

theorem hr2285_43 : rows 43 44 ≤ 1895245906429257 := rows_le_of_rowsJ 43 44 c2285_43_0

theorem c2285_44_0 : rowsJ 44 45 0 250 ≤ 1887643794472099 :=
  rowsJ_le_of_split 44 45 (by norm_num) (by norm_num) rows2285U_30 rows2285U_31 (by norm_num)

theorem hr2285_44 : rows 44 45 ≤ 1887643794472099 := rows_le_of_rowsJ 44 45 c2285_44_0

theorem c2285_45_0 : rowsJ 45 46 0 250 ≤ 1875427279818411 :=
  rowsJ_le_of_split 45 46 (by norm_num) (by norm_num) rows2285U_32 rows2285U_33 (by norm_num)

theorem hr2285_45 : rows 45 46 ≤ 1875427279818411 := rows_le_of_rowsJ 45 46 c2285_45_0

theorem c2285_46_0 : rowsJ 46 47 0 250 ≤ 1851777087217388 :=
  rowsJ_le_of_split 46 47 (by norm_num) (by norm_num) rows2285U_34 rows2285U_35 (by norm_num)

theorem hr2285_46 : rows 46 47 ≤ 1851777087217388 := rows_le_of_rowsJ 46 47 c2285_46_0

theorem c2285_47_0 : rowsJ 47 48 0 250 ≤ 1824026009273486 :=
  rowsJ_le_of_split 47 48 (by norm_num) (by norm_num) rows2285U_36 rows2285U_37 (by norm_num)

theorem hr2285_47 : rows 47 48 ≤ 1824026009273486 := rows_le_of_rowsJ 47 48 c2285_47_0

theorem c2285_48_0 : rowsJ 48 49 0 250 ≤ 1784836822111584 :=
  rowsJ_le_of_split 48 49 (by norm_num) (by norm_num) rows2285U_38 rows2285U_39 (by norm_num)

theorem hr2285_48 : rows 48 49 ≤ 1784836822111584 := rows_le_of_rowsJ 48 49 c2285_48_0

theorem c2285_49_0 : rowsJ 49 50 0 250 ≤ 1742713989738890 :=
  rowsJ_le_of_split 49 50 (by norm_num) (by norm_num) rows2285U_40 rows2285U_41 (by norm_num)

theorem hr2285_49 : rows 49 50 ≤ 1742713989738890 := rows_le_of_rowsJ 49 50 c2285_49_0

theorem c2285_50_0 : rowsJ 50 51 0 250 ≤ 1690082816096236 :=
  rowsJ_le_of_split 50 51 (by norm_num) (by norm_num) rows2285U_42 rows2285U_43 (by norm_num)

theorem hr2285_50 : rows 50 51 ≤ 1690082816096236 := rows_le_of_rowsJ 50 51 c2285_50_0

theorem c2285_51_0 : rowsJ 51 52 0 250 ≤ 1635344979045080 :=
  rowsJ_le_of_split 51 52 (by norm_num) (by norm_num) rows2285U_44 rows2285U_45 (by norm_num)

theorem hr2285_51 : rows 51 52 ≤ 1635344979045080 := rows_le_of_rowsJ 51 52 c2285_51_0

theorem c2285_52_0 : rowsJ 52 53 0 250 ≤ 1572287829080813 :=
  rowsJ_le_of_split 52 53 (by norm_num) (by norm_num) rows2285U_46 rows2285U_47 (by norm_num)

theorem hr2285_52 : rows 52 53 ≤ 1572287829080813 := rows_le_of_rowsJ 52 53 c2285_52_0

theorem c2285_53_0 : rowsJ 53 54 0 250 ≤ 1509144161986055 :=
  rowsJ_le_of_split 53 54 (by norm_num) (by norm_num) rows2285U_48 rows2285U_49 (by norm_num)

theorem hr2285_53 : rows 53 54 ≤ 1509144161986055 := rows_le_of_rowsJ 53 54 c2285_53_0

theorem c2285_54_0 : rowsJ 54 55 0 250 ≤ 1439358754216827 :=
  rowsJ_le_of_split 54 55 (by norm_num) (by norm_num) rows2285U_50 rows2285U_51 (by norm_num)

theorem hr2285_54 : rows 54 55 ≤ 1439358754216827 := rows_le_of_rowsJ 54 55 c2285_54_0

theorem c2285_55_0 : rowsJ 55 56 0 250 ≤ 1374499911262388 :=
  rowsJ_le_of_split 55 56 (by norm_num) (by norm_num) rows2285U_52 rows2285U_53 (by norm_num)

theorem hr2285_55 : rows 55 56 ≤ 1374499911262388 := rows_le_of_rowsJ 55 56 c2285_55_0

theorem c2285_56_0 : rowsJ 56 57 0 250 ≤ 1310389181052293 :=
  rowsJ_le_of_split 56 57 (by norm_num) (by norm_num) rows2285U_54 rows2285U_55 (by norm_num)

theorem hr2285_56 : rows 56 57 ≤ 1310389181052293 := rows_le_of_rowsJ 56 57 c2285_56_0

theorem c2285_57_0 : rowsJ 57 58 0 250 ≤ 1254882795633790 :=
  rowsJ_le_of_split 57 58 (by norm_num) (by norm_num) rows2285U_56 rows2285U_57 (by norm_num)

theorem hr2285_57 : rows 57 58 ≤ 1254882795633790 := rows_le_of_rowsJ 57 58 c2285_57_0

theorem c2285_58_0 : rowsJ 58 59 0 250 ≤ 1201323052180713 :=
  rowsJ_le_of_split 58 59 (by norm_num) (by norm_num) rows2285U_58 rows2285U_59 (by norm_num)

theorem hr2285_58 : rows 58 59 ≤ 1201323052180713 := rows_le_of_rowsJ 58 59 c2285_58_0

theorem c2285_59_1 : rowsJ 59 60 51 250 ≤ 45447980013884 :=
  rowsJ_le_of_split 59 60 (by norm_num) (by norm_num) rows2285U_61 rows2285U_62 (by norm_num)

theorem c2285_59_0 : rowsJ 59 60 0 250 ≤ 1156547949519534 :=
  rowsJ_le_of_split 59 60 (by norm_num) (by norm_num) rows2285U_60 c2285_59_1 (by norm_num)

theorem hr2285_59 : rows 59 60 ≤ 1156547949519534 := rows_le_of_rowsJ 59 60 c2285_59_0

theorem c2285_60_1 : rowsJ 60 61 51 250 ≤ 59112104851312 :=
  rowsJ_le_of_split 60 61 (by norm_num) (by norm_num) rows2285U_64 rows2285U_65 (by norm_num)

theorem c2285_60_0 : rowsJ 60 61 0 250 ≤ 1113127019012385 :=
  rowsJ_le_of_split 60 61 (by norm_num) (by norm_num) rows2285U_63 c2285_60_1 (by norm_num)

theorem hr2285_60 : rows 60 61 ≤ 1113127019012385 := rows_le_of_rowsJ 60 61 c2285_60_0

theorem c2285_61_1 : rowsJ 61 62 51 250 ≤ 71809995207258 :=
  rowsJ_le_of_split 61 62 (by norm_num) (by norm_num) rows2285U_67 rows2285U_68 (by norm_num)

theorem c2285_61_0 : rowsJ 61 62 0 250 ≤ 1075643037147085 :=
  rowsJ_le_of_split 61 62 (by norm_num) (by norm_num) rows2285U_66 c2285_61_1 (by norm_num)

theorem hr2285_61 : rows 61 62 ≤ 1075643037147085 := rows_le_of_rowsJ 61 62 c2285_61_0

theorem c2285_62_1 : rowsJ 62 63 51 250 ≤ 78944759281167 :=
  rowsJ_le_of_split 62 63 (by norm_num) (by norm_num) rows2285U_70 rows2285U_71 (by norm_num)

theorem c2285_62_0 : rowsJ 62 63 0 250 ≤ 1031674806385668 :=
  rowsJ_le_of_split 62 63 (by norm_num) (by norm_num) rows2285U_69 c2285_62_1 (by norm_num)

theorem hr2285_62 : rows 62 63 ≤ 1031674806385668 := rows_le_of_rowsJ 62 63 c2285_62_0

theorem c2285_63_2 : rowsJ 63 64 58 250 ≤ 59602255167596 :=
  rowsJ_le_of_split 63 64 (by norm_num) (by norm_num) rows2285U_74 rows2285U_75 (by norm_num)

theorem c2285_63_1 : rowsJ 63 64 51 250 ≤ 82750515370889 :=
  rowsJ_le_of_split 63 64 (by norm_num) (by norm_num) rows2285U_73 c2285_63_2 (by norm_num)

theorem c2285_63_0 : rowsJ 63 64 0 250 ≤ 990150821974071 :=
  rowsJ_le_of_split 63 64 (by norm_num) (by norm_num) rows2285U_72 c2285_63_1 (by norm_num)

theorem hr2285_63 : rows 63 64 ≤ 990150821974071 := rows_le_of_rowsJ 63 64 c2285_63_0

theorem c2285_64_2 : rowsJ 64 65 58 250 ≤ 59376461986914 :=
  rowsJ_le_of_split 64 65 (by norm_num) (by norm_num) rows2285U_78 rows2285U_79 (by norm_num)

theorem c2285_64_1 : rowsJ 64 65 51 250 ≤ 82296363195049 :=
  rowsJ_le_of_split 64 65 (by norm_num) (by norm_num) rows2285U_77 c2285_64_2 (by norm_num)

theorem c2285_64_0 : rowsJ 64 65 0 250 ≤ 943759829076447 :=
  rowsJ_le_of_split 64 65 (by norm_num) (by norm_num) rows2285U_76 c2285_64_1 (by norm_num)

theorem hr2285_64 : rows 64 65 ≤ 943759829076447 := rows_le_of_rowsJ 64 65 c2285_64_0

theorem c2285_65_2 : rowsJ 65 66 58 250 ≤ 56907919877456 :=
  rowsJ_le_of_split 65 66 (by norm_num) (by norm_num) rows2285U_82 rows2285U_83 (by norm_num)

theorem c2285_65_1 : rowsJ 65 66 51 250 ≤ 79604535283383 :=
  rowsJ_le_of_split 65 66 (by norm_num) (by norm_num) rows2285U_81 c2285_65_2 (by norm_num)

theorem c2285_65_0 : rowsJ 65 66 0 250 ≤ 900722303101865 :=
  rowsJ_le_of_split 65 66 (by norm_num) (by norm_num) rows2285U_80 c2285_65_1 (by norm_num)

theorem hr2285_65 : rows 65 66 ≤ 900722303101865 := rows_le_of_rowsJ 65 66 c2285_65_0

theorem c2285_66_2 : rowsJ 66 67 58 250 ≤ 51406855406419 :=
  rowsJ_le_of_split 66 67 (by norm_num) (by norm_num) rows2285U_86 rows2285U_87 (by norm_num)

theorem c2285_66_1 : rowsJ 66 67 51 250 ≤ 73881356604580 :=
  rowsJ_le_of_split 66 67 (by norm_num) (by norm_num) rows2285U_85 c2285_66_2 (by norm_num)

theorem c2285_66_0 : rowsJ 66 67 0 250 ≤ 852979751507144 :=
  rowsJ_le_of_split 66 67 (by norm_num) (by norm_num) rows2285U_84 c2285_66_1 (by norm_num)

theorem hr2285_66 : rows 66 67 ≤ 852979751507144 := rows_le_of_rowsJ 66 67 c2285_66_0

theorem c2285_67_2 : rowsJ 67 68 58 250 ≤ 44713514904416 :=
  rowsJ_le_of_split 67 68 (by norm_num) (by norm_num) rows2285U_90 rows2285U_91 (by norm_num)

theorem c2285_67_1 : rowsJ 67 68 51 250 ≤ 66970975348033 :=
  rowsJ_le_of_split 67 68 (by norm_num) (by norm_num) rows2285U_89 c2285_67_2 (by norm_num)

theorem c2285_67_0 : rowsJ 67 68 0 250 ≤ 809842087019058 :=
  rowsJ_le_of_split 67 68 (by norm_num) (by norm_num) rows2285U_88 c2285_67_1 (by norm_num)

theorem hr2285_67 : rows 67 68 ≤ 809842087019058 := rows_le_of_rowsJ 67 68 c2285_67_0

theorem c2285_68_2 : rowsJ 68 69 57 250 ≤ 43132547993790 :=
  rowsJ_le_of_split 68 69 (by norm_num) (by norm_num) rows2285U_94 rows2285U_95 (by norm_num)

theorem c2285_68_1 : rowsJ 68 69 50 250 ≤ 58348878438927 :=
  rowsJ_le_of_split 68 69 (by norm_num) (by norm_num) rows2285U_93 c2285_68_2 (by norm_num)

theorem c2285_68_0 : rowsJ 68 69 0 250 ≤ 763161324688321 :=
  rowsJ_le_of_split 68 69 (by norm_num) (by norm_num) rows2285U_92 c2285_68_1 (by norm_num)

theorem hr2285_68 : rows 68 69 ≤ 763161324688321 := rows_le_of_rowsJ 68 69 c2285_68_0

theorem c2285_69_2 : rowsJ 69 70 57 250 ≤ 35880769773291 :=
  rowsJ_le_of_split 69 70 (by norm_num) (by norm_num) rows2285U_98 rows2285U_99 (by norm_num)

theorem c2285_69_1 : rowsJ 69 70 50 250 ≤ 50950363608142 :=
  rowsJ_le_of_split 69 70 (by norm_num) (by norm_num) rows2285U_97 c2285_69_2 (by norm_num)

theorem c2285_69_0 : rowsJ 69 70 0 250 ≤ 722320760488167 :=
  rowsJ_le_of_split 69 70 (by norm_num) (by norm_num) rows2285U_96 c2285_69_1 (by norm_num)

theorem hr2285_69 : rows 69 70 ≤ 722320760488167 := rows_le_of_rowsJ 69 70 c2285_69_0

theorem c2285_70_2 : rowsJ 70 71 57 250 ≤ 30852889979409 :=
  rowsJ_le_of_split 70 71 (by norm_num) (by norm_num) rows2285U_102 rows2285U_103 (by norm_num)

theorem c2285_70_1 : rowsJ 70 71 50 250 ≤ 44860472768453 :=
  rowsJ_le_of_split 70 71 (by norm_num) (by norm_num) rows2285U_101 c2285_70_2 (by norm_num)

theorem c2285_70_0 : rowsJ 70 71 0 250 ≤ 681398837679404 :=
  rowsJ_le_of_split 70 71 (by norm_num) (by norm_num) rows2285U_100 c2285_70_1 (by norm_num)

theorem hr2285_70 : rows 70 71 ≤ 681398837679404 := rows_le_of_rowsJ 70 71 c2285_70_0

theorem c2285_71_3 : rowsJ 71 72 62 250 ≤ 17401635086804 :=
  rowsJ_le_of_split 71 72 (by norm_num) (by norm_num) rows2285U_107 rows2285U_108 (by norm_num)

theorem c2285_71_2 : rowsJ 71 72 56 250 ≤ 32913042442159 :=
  rowsJ_le_of_split 71 72 (by norm_num) (by norm_num) rows2285U_106 c2285_71_3 (by norm_num)

theorem c2285_71_1 : rowsJ 71 72 50 250 ≤ 42545992914343 :=
  rowsJ_le_of_split 71 72 (by norm_num) (by norm_num) rows2285U_105 c2285_71_2 (by norm_num)

theorem c2285_71_0 : rowsJ 71 72 0 250 ≤ 648556760975216 :=
  rowsJ_le_of_split 71 72 (by norm_num) (by norm_num) rows2285U_104 c2285_71_1 (by norm_num)

theorem hr2285_71 : rows 71 72 ≤ 648556760975216 := rows_le_of_rowsJ 71 72 c2285_71_0

theorem c2285_72_3 : rowsJ 72 73 62 250 ≤ 23752601509103 :=
  rowsJ_le_of_split 72 73 (by norm_num) (by norm_num) rows2285U_112 rows2285U_113 (by norm_num)

theorem c2285_72_2 : rowsJ 72 73 56 250 ≤ 35298469991333 :=
  rowsJ_le_of_split 72 73 (by norm_num) (by norm_num) rows2285U_111 c2285_72_3 (by norm_num)

theorem c2285_72_1 : rowsJ 72 73 50 250 ≤ 44069782386553 :=
  rowsJ_le_of_split 72 73 (by norm_num) (by norm_num) rows2285U_110 c2285_72_2 (by norm_num)

theorem c2285_72_0 : rowsJ 72 73 0 250 ≤ 616934364104903 :=
  rowsJ_le_of_split 72 73 (by norm_num) (by norm_num) rows2285U_109 c2285_72_1 (by norm_num)

theorem hr2285_72 : rows 72 73 ≤ 616934364104903 := rows_le_of_rowsJ 72 73 c2285_72_0

theorem c2285_73_3 : rowsJ 73 74 63 250 ≤ 35050529321749 :=
  rowsJ_le_of_split 73 74 (by norm_num) (by norm_num) rows2285U_117 rows2285U_118 (by norm_num)

theorem c2285_73_2 : rowsJ 73 74 56 250 ≤ 43837953847169 :=
  rowsJ_le_of_split 73 74 (by norm_num) (by norm_num) rows2285U_116 c2285_73_3 (by norm_num)

theorem c2285_73_1 : rowsJ 73 74 49 250 ≤ 51846794080021 :=
  rowsJ_le_of_split 73 74 (by norm_num) (by norm_num) rows2285U_115 c2285_73_2 (by norm_num)

theorem c2285_73_0 : rowsJ 73 74 0 250 ≤ 596063841896923 :=
  rowsJ_le_of_split 73 74 (by norm_num) (by norm_num) rows2285U_114 c2285_73_1 (by norm_num)

theorem hr2285_73 : rows 73 74 ≤ 596063841896923 := rows_le_of_rowsJ 73 74 c2285_73_0

theorem c2285_74_3 : rowsJ 74 75 63 250 ≤ 282216299760683 :=
  rowsJ_le_of_split 74 75 (by norm_num) (by norm_num) rows2285U_122 rows2285U_123 (by norm_num)

theorem c2285_74_2 : rowsJ 74 75 56 250 ≤ 287928699922276 :=
  rowsJ_le_of_split 74 75 (by norm_num) (by norm_num) rows2285U_121 c2285_74_3 (by norm_num)

theorem c2285_74_1 : rowsJ 74 75 49 250 ≤ 294646545555476 :=
  rowsJ_le_of_split 74 75 (by norm_num) (by norm_num) rows2285U_120 c2285_74_2 (by norm_num)

theorem c2285_74_0 : rowsJ 74 75 0 250 ≤ 807508202685153 :=
  rowsJ_le_of_split 74 75 (by norm_num) (by norm_num) rows2285U_119 c2285_74_1 (by norm_num)

theorem hr2285_74 : rows 74 75 ≤ 807508202685153 := rows_le_of_rowsJ 74 75 c2285_74_0

theorem c2285_75_2 : rowsJ 75 76 56 250 ≤ 759645203589225 :=
  rowsJ_le_of_split 75 76 (by norm_num) (by norm_num) rows2285U_126 rows2285U_127 (by norm_num)

theorem c2285_75_1 : rowsJ 75 76 49 250 ≤ 765265458110903 :=
  rowsJ_le_of_split 75 76 (by norm_num) (by norm_num) rows2285U_125 c2285_75_2 (by norm_num)

theorem c2285_75_0 : rowsJ 75 76 0 250 ≤ 1251044058128890 :=
  rowsJ_le_of_split 75 76 (by norm_num) (by norm_num) rows2285U_124 c2285_75_1 (by norm_num)

theorem hr2285_75 : rows 75 76 ≤ 1251044058128890 := rows_le_of_rowsJ 75 76 c2285_75_0

theorem c2285_76_2 : rowsJ 76 77 56 250 ≤ 753062437598860 :=
  rowsJ_le_of_split 76 77 (by norm_num) (by norm_num) rows2285U_130 rows2285U_131 (by norm_num)

theorem c2285_76_1 : rowsJ 76 77 49 250 ≤ 757285199132039 :=
  rowsJ_le_of_split 76 77 (by norm_num) (by norm_num) rows2285U_129 c2285_76_2 (by norm_num)

theorem c2285_76_0 : rowsJ 76 77 0 250 ≤ 1213623955555481 :=
  rowsJ_le_of_split 76 77 (by norm_num) (by norm_num) rows2285U_128 c2285_76_1 (by norm_num)

theorem hr2285_76 : rows 76 77 ≤ 1213623955555481 := rows_le_of_rowsJ 76 77 c2285_76_0

theorem c2285_77_2 : rowsJ 77 78 55 250 ≤ 749011470317630 :=
  rowsJ_le_of_split 77 78 (by norm_num) (by norm_num) rows2285U_134 rows2285U_135 (by norm_num)

theorem c2285_77_1 : rowsJ 77 78 48 250 ≤ 751694852347139 :=
  rowsJ_le_of_split 77 78 (by norm_num) (by norm_num) rows2285U_133 c2285_77_2 (by norm_num)

theorem c2285_77_0 : rowsJ 77 78 0 250 ≤ 1182892158771827 :=
  rowsJ_le_of_split 77 78 (by norm_num) (by norm_num) rows2285U_132 c2285_77_1 (by norm_num)

theorem hr2285_77 : rows 77 78 ≤ 1182892158771827 := rows_le_of_rowsJ 77 78 c2285_77_0

theorem c2285_78_2 : rowsJ 78 79 55 250 ≤ 505204722499742 :=
  rowsJ_le_of_split 78 79 (by norm_num) (by norm_num) rows2285U_138 rows2285U_139 (by norm_num)

theorem c2285_78_1 : rowsJ 78 79 48 250 ≤ 506927322316240 :=
  rowsJ_le_of_split 78 79 (by norm_num) (by norm_num) rows2285U_137 c2285_78_2 (by norm_num)

theorem c2285_78_0 : rowsJ 78 79 0 250 ≤ 910811431536383 :=
  rowsJ_le_of_split 78 79 (by norm_num) (by norm_num) rows2285U_136 c2285_78_1 (by norm_num)

theorem hr2285_78 : rows 78 79 ≤ 910811431536383 := rows_le_of_rowsJ 78 79 c2285_78_0

theorem c2285_79_2 : rowsJ 79 80 55 250 ≤ 501353480336973 :=
  rowsJ_le_of_split 79 80 (by norm_num) (by norm_num) rows2285U_142 rows2285U_143 (by norm_num)

theorem c2285_79_1 : rowsJ 79 80 48 250 ≤ 502389915991036 :=
  rowsJ_le_of_split 79 80 (by norm_num) (by norm_num) rows2285U_141 c2285_79_2 (by norm_num)

theorem c2285_79_0 : rowsJ 79 80 0 250 ≤ 884020285068160 :=
  rowsJ_le_of_split 79 80 (by norm_num) (by norm_num) rows2285U_140 c2285_79_1 (by norm_num)

theorem hr2285_79 : rows 79 80 ≤ 884020285068160 := rows_le_of_rowsJ 79 80 c2285_79_0

theorem c2285_80_2 : rowsJ 80 81 55 250 ≤ 255036003853987 :=
  rowsJ_le_of_split 80 81 (by norm_num) (by norm_num) rows2285U_146 rows2285U_147 (by norm_num)

theorem c2285_80_1 : rowsJ 80 81 48 250 ≤ 255440535528152 :=
  rowsJ_le_of_split 80 81 (by norm_num) (by norm_num) rows2285U_145 c2285_80_2 (by norm_num)

theorem c2285_80_0 : rowsJ 80 81 0 250 ≤ 612849800518755 :=
  rowsJ_le_of_split 80 81 (by norm_num) (by norm_num) rows2285U_144 c2285_80_1 (by norm_num)

theorem hr2285_80 : rows 80 81 ≤ 612849800518755 := rows_le_of_rowsJ 80 81 c2285_80_0

theorem c2285_81_2 : rowsJ 81 82 54 250 ≤ 251767404319816 :=
  rowsJ_le_of_split 81 82 (by norm_num) (by norm_num) rows2285U_150 rows2285U_151 (by norm_num)

theorem c2285_81_1 : rowsJ 81 82 47 250 ≤ 251900782075543 :=
  rowsJ_le_of_split 81 82 (by norm_num) (by norm_num) rows2285U_149 c2285_81_2 (by norm_num)

theorem c2285_81_0 : rowsJ 81 82 0 250 ≤ 590473818148019 :=
  rowsJ_le_of_split 81 82 (by norm_num) (by norm_num) rows2285U_148 c2285_81_1 (by norm_num)

theorem hr2285_81 : rows 81 82 ≤ 590473818148019 := rows_le_of_rowsJ 81 82 c2285_81_0

theorem c2285_82_2 : rowsJ 82 83 54 250 ≤ 2722336624377 :=
  rowsJ_le_of_split 82 83 (by norm_num) (by norm_num) rows2285U_154 rows2285U_155 (by norm_num)

theorem c2285_82_1 : rowsJ 82 83 47 250 ≤ 2722336624377 :=
  rowsJ_le_of_split 82 83 (by norm_num) (by norm_num) rows2285U_153 c2285_82_2 (by norm_num)

theorem c2285_82_0 : rowsJ 82 83 0 250 ≤ 321212842252555 :=
  rowsJ_le_of_split 82 83 (by norm_num) (by norm_num) rows2285U_152 c2285_82_1 (by norm_num)

theorem hr2285_82 : rows 82 83 ≤ 321212842252555 := rows_le_of_rowsJ 82 83 c2285_82_0

theorem c2285_83_2 : rowsJ 83 84 54 250 ≤ 0 :=
  rowsJ_le_of_split 83 84 (by norm_num) (by norm_num) rows2285U_158 rows2285U_159 (by norm_num)

theorem c2285_83_1 : rowsJ 83 84 47 250 ≤ 0 :=
  rowsJ_le_of_split 83 84 (by norm_num) (by norm_num) rows2285U_157 c2285_83_2 (by norm_num)

theorem c2285_83_0 : rowsJ 83 84 0 250 ≤ 304145355421189 :=
  rowsJ_le_of_split 83 84 (by norm_num) (by norm_num) rows2285U_156 c2285_83_1 (by norm_num)

theorem hr2285_83 : rows 83 84 ≤ 304145355421189 := rows_le_of_rowsJ 83 84 c2285_83_0

theorem c2285_84_2 : rowsJ 84 85 54 250 ≤ 0 :=
  rowsJ_le_of_split 84 85 (by norm_num) (by norm_num) rows2285U_162 rows2285U_163 (by norm_num)

theorem c2285_84_1 : rowsJ 84 85 47 250 ≤ 0 :=
  rowsJ_le_of_split 84 85 (by norm_num) (by norm_num) rows2285U_161 c2285_84_2 (by norm_num)

theorem c2285_84_0 : rowsJ 84 85 0 250 ≤ 288829793561832 :=
  rowsJ_le_of_split 84 85 (by norm_num) (by norm_num) rows2285U_160 c2285_84_1 (by norm_num)

theorem hr2285_84 : rows 84 85 ≤ 288829793561832 := rows_le_of_rowsJ 84 85 c2285_84_0

theorem c2285_85_2 : rowsJ 85 86 53 250 ≤ 0 :=
  rowsJ_le_of_split 85 86 (by norm_num) (by norm_num) rows2285U_166 rows2285U_167 (by norm_num)

theorem c2285_85_1 : rowsJ 85 86 46 250 ≤ 0 :=
  rowsJ_le_of_split 85 86 (by norm_num) (by norm_num) rows2285U_165 c2285_85_2 (by norm_num)

theorem c2285_85_0 : rowsJ 85 86 0 250 ≤ 280158371509662 :=
  rowsJ_le_of_split 85 86 (by norm_num) (by norm_num) rows2285U_164 c2285_85_1 (by norm_num)

theorem hr2285_85 : rows 85 86 ≤ 280158371509662 := rows_le_of_rowsJ 85 86 c2285_85_0

theorem c2285_86_2 : rowsJ 86 87 54 250 ≤ 0 :=
  rowsJ_le_of_split 86 87 (by norm_num) (by norm_num) rows2285U_170 rows2285U_171 (by norm_num)

theorem c2285_86_1 : rowsJ 86 87 46 250 ≤ 1472998128878 :=
  rowsJ_le_of_split 86 87 (by norm_num) (by norm_num) rows2285U_169 c2285_86_2 (by norm_num)

theorem c2285_86_0 : rowsJ 86 87 0 250 ≤ 270838354240937 :=
  rowsJ_le_of_split 86 87 (by norm_num) (by norm_num) rows2285U_168 c2285_86_1 (by norm_num)

theorem hr2285_86 : rows 86 87 ≤ 270838354240937 := rows_le_of_rowsJ 86 87 c2285_86_0

theorem c2285_87_1 : rowsJ 87 88 46 250 ≤ 4750288976003 :=
  rowsJ_le_of_split 87 88 (by norm_num) (by norm_num) rows2285U_173 rows2285U_174 (by norm_num)

theorem c2285_87_0 : rowsJ 87 88 0 250 ≤ 268608249891473 :=
  rowsJ_le_of_split 87 88 (by norm_num) (by norm_num) rows2285U_172 c2285_87_1 (by norm_num)

theorem hr2285_87 : rows 87 88 ≤ 268608249891473 := rows_le_of_rowsJ 87 88 c2285_87_0

theorem c2285_88_1 : rowsJ 88 89 45 250 ≤ 15013998091247 :=
  rowsJ_le_of_split 88 89 (by norm_num) (by norm_num) rows2285U_176 rows2285U_177 (by norm_num)

theorem c2285_88_0 : rowsJ 88 89 0 250 ≤ 266068615411539 :=
  rowsJ_le_of_split 88 89 (by norm_num) (by norm_num) rows2285U_175 c2285_88_1 (by norm_num)

theorem hr2285_88 : rows 88 89 ≤ 266068615411539 := rows_le_of_rowsJ 88 89 c2285_88_0

theorem c2285_89_1 : rowsJ 89 90 45 250 ≤ 22451108565487 :=
  rowsJ_le_of_split 89 90 (by norm_num) (by norm_num) rows2285U_179 rows2285U_180 (by norm_num)

theorem c2285_89_0 : rowsJ 89 90 0 250 ≤ 269938794531443 :=
  rowsJ_le_of_split 89 90 (by norm_num) (by norm_num) rows2285U_178 c2285_89_1 (by norm_num)

theorem hr2285_89 : rows 89 90 ≤ 269938794531443 := rows_le_of_rowsJ 89 90 c2285_89_0

theorem c2285_90_1 : rowsJ 90 91 45 250 ≤ 29918844063318 :=
  rowsJ_le_of_split 90 91 (by norm_num) (by norm_num) rows2285U_182 rows2285U_183 (by norm_num)

theorem c2285_90_0 : rowsJ 90 91 0 250 ≤ 272185836524886 :=
  rowsJ_le_of_split 90 91 (by norm_num) (by norm_num) rows2285U_181 c2285_90_1 (by norm_num)

theorem hr2285_90 : rows 90 91 ≤ 272185836524886 := rows_le_of_rowsJ 90 91 c2285_90_0

theorem c2285_91_1 : rowsJ 91 92 44 250 ≤ 49125752021468 :=
  rowsJ_le_of_split 91 92 (by norm_num) (by norm_num) rows2285U_185 rows2285U_186 (by norm_num)

theorem c2285_91_0 : rowsJ 91 92 0 250 ≤ 280561560177179 :=
  rowsJ_le_of_split 91 92 (by norm_num) (by norm_num) rows2285U_184 c2285_91_1 (by norm_num)

theorem hr2285_91 : rows 91 92 ≤ 280561560177179 := rows_le_of_rowsJ 91 92 c2285_91_0

theorem c2285_92_1 : rowsJ 92 93 44 250 ≤ 57699461921536 :=
  rowsJ_le_of_split 92 93 (by norm_num) (by norm_num) rows2285U_188 rows2285U_189 (by norm_num)

theorem c2285_92_0 : rowsJ 92 93 0 250 ≤ 286058290531216 :=
  rowsJ_le_of_split 92 93 (by norm_num) (by norm_num) rows2285U_187 c2285_92_1 (by norm_num)

theorem hr2285_92 : rows 92 93 ≤ 286058290531216 := rows_le_of_rowsJ 92 93 c2285_92_0

theorem c2285_93_1 : rowsJ 93 94 44 250 ≤ 66343983662069 :=
  rowsJ_le_of_split 93 94 (by norm_num) (by norm_num) rows2285U_191 rows2285U_192 (by norm_num)

theorem c2285_93_0 : rowsJ 93 94 0 250 ≤ 296748512932299 :=
  rowsJ_le_of_split 93 94 (by norm_num) (by norm_num) rows2285U_190 c2285_93_1 (by norm_num)

theorem hr2285_93 : rows 93 94 ≤ 296748512932299 := rows_le_of_rowsJ 93 94 c2285_93_0

theorem c2285_94_1 : rowsJ 94 95 44 250 ≤ 72601919018205 :=
  rowsJ_le_of_split 94 95 (by norm_num) (by norm_num) rows2285U_194 rows2285U_195 (by norm_num)

theorem c2285_94_0 : rowsJ 94 95 0 250 ≤ 304084638818606 :=
  rowsJ_le_of_split 94 95 (by norm_num) (by norm_num) rows2285U_193 c2285_94_1 (by norm_num)

theorem hr2285_94 : rows 94 95 ≤ 304084638818606 := rows_le_of_rowsJ 94 95 c2285_94_0

theorem c2285_95_1 : rowsJ 95 96 43 250 ≤ 96486934456718 :=
  rowsJ_le_of_split 95 96 (by norm_num) (by norm_num) rows2285U_197 rows2285U_198 (by norm_num)

theorem c2285_95_0 : rowsJ 95 96 0 250 ≤ 315692685583833 :=
  rowsJ_le_of_split 95 96 (by norm_num) (by norm_num) rows2285U_196 c2285_95_1 (by norm_num)

theorem hr2285_95 : rows 95 96 ≤ 315692685583833 := rows_le_of_rowsJ 95 96 c2285_95_0

theorem c2285_96_1 : rowsJ 96 97 43 250 ≤ 246238989253742 :=
  rowsJ_le_of_split 96 97 (by norm_num) (by norm_num) rows2285U_200 rows2285U_201 (by norm_num)

theorem c2285_96_0 : rowsJ 96 97 0 250 ≤ 468506220562543 :=
  rowsJ_le_of_split 96 97 (by norm_num) (by norm_num) rows2285U_199 c2285_96_1 (by norm_num)

theorem hr2285_96 : rows 96 97 ≤ 468506220562543 := rows_le_of_rowsJ 96 97 c2285_96_0

theorem c2285_97_1 : rowsJ 97 98 43 250 ≤ 536815291186734 :=
  rowsJ_le_of_split 97 98 (by norm_num) (by norm_num) rows2285U_203 rows2285U_204 (by norm_num)

theorem c2285_97_0 : rowsJ 97 98 0 250 ≤ 767344757542694 :=
  rowsJ_le_of_split 97 98 (by norm_num) (by norm_num) rows2285U_202 c2285_97_1 (by norm_num)

theorem hr2285_97 : rows 97 98 ≤ 767344757542694 := rows_le_of_rowsJ 97 98 c2285_97_0

theorem c2285_98_1 : rowsJ 98 99 42 250 ≤ 841901284443735 :=
  rowsJ_le_of_split 98 99 (by norm_num) (by norm_num) rows2285U_206 rows2285U_207 (by norm_num)

theorem c2285_98_0 : rowsJ 98 99 0 250 ≤ 1056303655408922 :=
  rowsJ_le_of_split 98 99 (by norm_num) (by norm_num) rows2285U_205 c2285_98_1 (by norm_num)

theorem hr2285_98 : rows 98 99 ≤ 1056303655408922 := rows_le_of_rowsJ 98 99 c2285_98_0

theorem c2285_99_0 : rowsJ 99 100 0 250 ≤ 1344508223743116 :=
  rowsJ_le_of_split 99 100 (by norm_num) (by norm_num) rows2285U_208 rows2285U_209 (by norm_num)

theorem hr2285_99 : rows 99 100 ≤ 1344508223743116 := rows_le_of_rowsJ 99 100 c2285_99_0

theorem c2285_100_0 : rowsJ 100 101 0 250 ≤ 1624069813607412 :=
  rowsJ_le_of_split 100 101 (by norm_num) (by norm_num) rows2285U_210 rows2285U_211 (by norm_num)

theorem hr2285_100 : rows 100 101 ≤ 1624069813607412 := rows_le_of_rowsJ 100 101 c2285_100_0

theorem c2285_101_0 : rowsJ 101 102 0 250 ≤ 1903057695527075 :=
  rowsJ_le_of_split 101 102 (by norm_num) (by norm_num) rows2285U_212 rows2285U_213 (by norm_num)

theorem hr2285_101 : rows 101 102 ≤ 1903057695527075 := rows_le_of_rowsJ 101 102 c2285_101_0

theorem c2285_102_0 : rowsJ 102 103 0 250 ≤ 2173763843430562 :=
  rowsJ_le_of_split 102 103 (by norm_num) (by norm_num) rows2285U_214 rows2285U_215 (by norm_num)

theorem hr2285_102 : rows 102 103 ≤ 2173763843430562 := rows_le_of_rowsJ 102 103 c2285_102_0

theorem c2285_103_0 : rowsJ 103 104 0 250 ≤ 2444856818185289 :=
  rowsJ_le_of_split 103 104 (by norm_num) (by norm_num) rows2285U_216 rows2285U_217 (by norm_num)

theorem hr2285_103 : rows 103 104 ≤ 2444856818185289 := rows_le_of_rowsJ 103 104 c2285_103_0

theorem c2285_104_0 : rowsJ 104 105 0 250 ≤ 2707974883633403 :=
  rowsJ_le_of_split 104 105 (by norm_num) (by norm_num) rows2285U_218 rows2285U_219 (by norm_num)

theorem hr2285_104 : rows 104 105 ≤ 2707974883633403 := rows_le_of_rowsJ 104 105 c2285_104_0

theorem c2285_105_0 : rowsJ 105 106 0 250 ≤ 2947237910204873 :=
  rowsJ_le_of_split 105 106 (by norm_num) (by norm_num) rows2285U_220 rows2285U_221 (by norm_num)

theorem hr2285_105 : rows 105 106 ≤ 2947237910204873 := rows_le_of_rowsJ 105 106 c2285_105_0

theorem c2285_106_0 : rowsJ 106 107 0 250 ≤ 3195226132499039 :=
  rowsJ_le_of_split 106 107 (by norm_num) (by norm_num) rows2285U_222 rows2285U_223 (by norm_num)

theorem hr2285_106 : rows 106 107 ≤ 3195226132499039 := rows_le_of_rowsJ 106 107 c2285_106_0

theorem c2285_107_0 : rowsJ 107 108 0 250 ≤ 3445668624152650 :=
  rowsJ_le_of_split 107 108 (by norm_num) (by norm_num) rows2285U_224 rows2285U_225 (by norm_num)

theorem hr2285_107 : rows 107 108 ≤ 3445668624152650 := rows_le_of_rowsJ 107 108 c2285_107_0

theorem c2285_108_0 : rowsJ 108 109 0 250 ≤ 3679055989998842 :=
  rowsJ_le_of_split 108 109 (by norm_num) (by norm_num) rows2285U_226 rows2285U_227 (by norm_num)

theorem hr2285_108 : rows 108 109 ≤ 3679055989998842 := rows_le_of_rowsJ 108 109 c2285_108_0

theorem c2285_109_0 : rowsJ 109 110 0 250 ≤ 3928748250226106 :=
  rowsJ_le_of_split 109 110 (by norm_num) (by norm_num) rows2285U_228 rows2285U_229 (by norm_num)

theorem hr2285_109 : rows 109 110 ≤ 3928748250226106 := rows_le_of_rowsJ 109 110 c2285_109_0

theorem c2285_110_0 : rowsJ 110 111 0 250 ≤ 4174201740272375 :=
  rowsJ_le_of_split 110 111 (by norm_num) (by norm_num) rows2285U_230 rows2285U_231 (by norm_num)

theorem hr2285_110 : rows 110 111 ≤ 4174201740272375 := rows_le_of_rowsJ 110 111 c2285_110_0

theorem c2285_111_0 : rowsJ 111 112 0 250 ≤ 4409550899118809 :=
  rowsJ_le_of_split 111 112 (by norm_num) (by norm_num) rows2285U_232 rows2285U_233 (by norm_num)

theorem hr2285_111 : rows 111 112 ≤ 4409550899118809 := rows_le_of_rowsJ 111 112 c2285_111_0

theorem c2285_112_0 : rowsJ 112 113 0 250 ≤ 4549153878002443 :=
  rowsJ_le_of_split 112 113 (by norm_num) (by norm_num) rows2285U_234 rows2285U_235 (by norm_num)

theorem hr2285_112 : rows 112 113 ≤ 4549153878002443 := rows_le_of_rowsJ 112 113 c2285_112_0

theorem t2285_104 : rows 169 250 ≤ 534993981916169913 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_250 rows2285U_251 (by norm_num)

theorem t2285_103 : rows 134 250 ≤ 888156730611840239 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_249 t2285_104 (by norm_num)

theorem t2285_102 : rows 129 250 ≤ 914618069834137896 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_248 t2285_103 (by norm_num)

theorem t2285_101 : rows 126 250 ≤ 929613493057626963 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_247 t2285_102 (by norm_num)

theorem t2285_100 : rows 124 250 ≤ 939429886091997304 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_246 t2285_101 (by norm_num)

theorem t2285_99 : rows 122 250 ≤ 949129427551480443 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_245 t2285_100 (by norm_num)

theorem t2285_98 : rows 121 250 ≤ 953944827046670341 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_244 t2285_99 (by norm_num)

theorem t2285_97 : rows 120 250 ≤ 958729484932980053 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_243 t2285_98 (by norm_num)

theorem t2285_96 : rows 119 250 ≤ 963497218201285698 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_242 t2285_97 (by norm_num)

theorem t2285_95 : rows 118 250 ≤ 968231330109299954 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_241 t2285_96 (by norm_num)

theorem t2285_94 : rows 117 250 ≤ 972933212175741827 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_240 t2285_95 (by norm_num)

theorem t2285_93 : rows 116 250 ≤ 977611932783480358 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_239 t2285_94 (by norm_num)

theorem t2285_92 : rows 115 250 ≤ 982257167529623742 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_238 t2285_93 (by norm_num)

theorem t2285_91 : rows 114 250 ≤ 986865307367932155 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_237 t2285_92 (by norm_num)

theorem t2285_90 : rows 113 250 ≤ 991451853446615970 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_236 t2285_91 (by norm_num)

theorem t2285_89 : rows 112 250 ≤ 996001007324618413 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_112 t2285_90 (by norm_num)

theorem t2285_88 : rows 111 250 ≤ 1000410558223737222 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_111 t2285_89 (by norm_num)

theorem t2285_87 : rows 110 250 ≤ 1004584759964009597 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_110 t2285_88 (by norm_num)

theorem t2285_86 : rows 109 250 ≤ 1008513508214235703 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_109 t2285_87 (by norm_num)

theorem t2285_85 : rows 108 250 ≤ 1012192564204234545 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_108 t2285_86 (by norm_num)

theorem t2285_84 : rows 107 250 ≤ 1015638232828387195 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_107 t2285_85 (by norm_num)

theorem t2285_83 : rows 106 250 ≤ 1018833458960886234 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_106 t2285_84 (by norm_num)

theorem t2285_82 : rows 105 250 ≤ 1021780696871091107 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_105 t2285_83 (by norm_num)

theorem t2285_81 : rows 104 250 ≤ 1024488671754724510 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_104 t2285_82 (by norm_num)

theorem t2285_80 : rows 103 250 ≤ 1026933528572909799 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_103 t2285_81 (by norm_num)

theorem t2285_79 : rows 102 250 ≤ 1029107292416340361 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_102 t2285_80 (by norm_num)

theorem t2285_78 : rows 101 250 ≤ 1031010350111867436 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_101 t2285_79 (by norm_num)

theorem t2285_77 : rows 100 250 ≤ 1032634419925474848 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_100 t2285_78 (by norm_num)

theorem t2285_76 : rows 99 250 ≤ 1033978928149217964 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_99 t2285_77 (by norm_num)

theorem t2285_75 : rows 98 250 ≤ 1035035231804626886 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_98 t2285_76 (by norm_num)

theorem t2285_74 : rows 97 250 ≤ 1035802576562169580 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_97 t2285_75 (by norm_num)

theorem t2285_73 : rows 96 250 ≤ 1036271082782732123 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_96 t2285_74 (by norm_num)

theorem t2285_72 : rows 95 250 ≤ 1036586775468315956 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_95 t2285_73 (by norm_num)

theorem t2285_71 : rows 94 250 ≤ 1036890860107134562 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_94 t2285_72 (by norm_num)

theorem t2285_70 : rows 93 250 ≤ 1037187608620066861 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_93 t2285_71 (by norm_num)

theorem t2285_69 : rows 92 250 ≤ 1037473666910598077 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_92 t2285_70 (by norm_num)

theorem t2285_68 : rows 91 250 ≤ 1037754228470775256 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_91 t2285_69 (by norm_num)

theorem t2285_67 : rows 90 250 ≤ 1038026414307300142 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_90 t2285_68 (by norm_num)

theorem t2285_66 : rows 89 250 ≤ 1038296353101831585 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_89 t2285_67 (by norm_num)

theorem t2285_65 : rows 88 250 ≤ 1038562421717243124 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_88 t2285_66 (by norm_num)

theorem t2285_64 : rows 87 250 ≤ 1038831029967134597 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_87 t2285_65 (by norm_num)

theorem t2285_63 : rows 86 250 ≤ 1039101868321375534 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_86 t2285_64 (by norm_num)

theorem t2285_62 : rows 85 250 ≤ 1039382026692885196 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_85 t2285_63 (by norm_num)

theorem t2285_61 : rows 84 250 ≤ 1039670856486447028 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_84 t2285_62 (by norm_num)

theorem t2285_60 : rows 83 250 ≤ 1039975001841868217 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_83 t2285_61 (by norm_num)

theorem t2285_59 : rows 82 250 ≤ 1040296214684120772 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_82 t2285_60 (by norm_num)

theorem t2285_58 : rows 81 250 ≤ 1040886688502268791 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_81 t2285_59 (by norm_num)

theorem t2285_57 : rows 80 250 ≤ 1041499538302787546 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_80 t2285_58 (by norm_num)

theorem t2285_56 : rows 79 250 ≤ 1042383558587855706 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_79 t2285_57 (by norm_num)

theorem t2285_55 : rows 78 250 ≤ 1043294370019392089 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_78 t2285_56 (by norm_num)

theorem t2285_54 : rows 77 250 ≤ 1044477262178163916 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_77 t2285_55 (by norm_num)

theorem t2285_53 : rows 76 250 ≤ 1045690886133719397 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_76 t2285_54 (by norm_num)

theorem t2285_52 : rows 75 250 ≤ 1046941930191848287 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_75 t2285_53 (by norm_num)

theorem t2285_51 : rows 74 250 ≤ 1047749438394533440 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_74 t2285_52 (by norm_num)

theorem t2285_50 : rows 73 250 ≤ 1048345502236430363 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_73 t2285_51 (by norm_num)

theorem t2285_49 : rows 72 250 ≤ 1048962436600535266 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_72 t2285_50 (by norm_num)

theorem t2285_48 : rows 71 250 ≤ 1049610993361510482 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_71 t2285_49 (by norm_num)

theorem t2285_47 : rows 70 250 ≤ 1050292392199189886 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_70 t2285_48 (by norm_num)

theorem t2285_46 : rows 69 250 ≤ 1051014712959678053 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_69 t2285_47 (by norm_num)

theorem t2285_45 : rows 68 250 ≤ 1051777874284366374 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_68 t2285_46 (by norm_num)

theorem t2285_44 : rows 67 250 ≤ 1052587716371385432 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_67 t2285_45 (by norm_num)

theorem t2285_43 : rows 66 250 ≤ 1053440696122892576 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_66 t2285_44 (by norm_num)

theorem t2285_42 : rows 65 250 ≤ 1054341418425994441 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_65 t2285_43 (by norm_num)

theorem t2285_41 : rows 64 250 ≤ 1055285178255070888 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_64 t2285_42 (by norm_num)

theorem t2285_40 : rows 63 250 ≤ 1056275329077044959 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_63 t2285_41 (by norm_num)

theorem t2285_39 : rows 62 250 ≤ 1057307003883430627 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_62 t2285_40 (by norm_num)

theorem t2285_38 : rows 61 250 ≤ 1058382646920577712 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_61 t2285_39 (by norm_num)

theorem t2285_37 : rows 60 250 ≤ 1059495773939590097 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_60 t2285_38 (by norm_num)

theorem t2285_36 : rows 59 250 ≤ 1060652321889109631 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_59 t2285_37 (by norm_num)

theorem t2285_35 : rows 58 250 ≤ 1061853644941290344 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_58 t2285_36 (by norm_num)

theorem t2285_34 : rows 57 250 ≤ 1063108527736924134 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_57 t2285_35 (by norm_num)

theorem t2285_33 : rows 56 250 ≤ 1064418916917976427 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_56 t2285_34 (by norm_num)

theorem t2285_32 : rows 55 250 ≤ 1065793416829238815 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_55 t2285_33 (by norm_num)

theorem t2285_31 : rows 54 250 ≤ 1067232775583455642 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_54 t2285_32 (by norm_num)

theorem t2285_30 : rows 53 250 ≤ 1068741919745441697 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_53 t2285_31 (by norm_num)

theorem t2285_29 : rows 52 250 ≤ 1070314207574522510 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_52 t2285_30 (by norm_num)

theorem t2285_28 : rows 51 250 ≤ 1071949552553567590 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_51 t2285_29 (by norm_num)

theorem t2285_27 : rows 50 250 ≤ 1073639635369663826 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_50 t2285_28 (by norm_num)

theorem t2285_26 : rows 49 250 ≤ 1075382349359402716 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_49 t2285_27 (by norm_num)

theorem t2285_25 : rows 48 250 ≤ 1077167186181514300 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_48 t2285_26 (by norm_num)

theorem t2285_24 : rows 47 250 ≤ 1078991212190787786 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_47 t2285_25 (by norm_num)

theorem t2285_23 : rows 46 250 ≤ 1080842989278005174 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_46 t2285_24 (by norm_num)

theorem t2285_22 : rows 45 250 ≤ 1082718416557823585 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_45 t2285_23 (by norm_num)

theorem t2285_21 : rows 44 250 ≤ 1084606060352295684 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_44 t2285_22 (by norm_num)

theorem t2285_20 : rows 43 250 ≤ 1086501306258724941 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_43 t2285_21 (by norm_num)

theorem t2285_19 : rows 42 250 ≤ 1088391842387058763 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_42 t2285_20 (by norm_num)

theorem t2285_18 : rows 41 250 ≤ 1090273191647170735 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_41 t2285_19 (by norm_num)

theorem t2285_17 : rows 40 250 ≤ 1092132681858939151 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_40 t2285_18 (by norm_num)

theorem t2285_16 : rows 39 250 ≤ 1093965041148500890 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_39 t2285_17 (by norm_num)

theorem t2285_15 : rows 38 250 ≤ 1095758224988437161 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_38 t2285_16 (by norm_num)

theorem t2285_14 : rows 37 250 ≤ 1097507628820380673 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_37 t2285_15 (by norm_num)

theorem t2285_13 : rows 36 250 ≤ 1099201518693950995 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_36 t2285_14 (by norm_num)

theorem t2285_12 : rows 35 250 ≤ 1100853334438993227 :=
  rows_le_of_split (by norm_num) (by norm_num) hr2285_35 t2285_13 (by norm_num)

theorem t2285_11 : rows 34 250 ≤ 1102495942437682704 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_11 t2285_12 (by norm_num)

theorem t2285_10 : rows 33 250 ≤ 1104157770693716018 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_10 t2285_11 (by norm_num)

theorem t2285_9 : rows 32 250 ≤ 1105861051355532625 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_9 t2285_10 (by norm_num)

theorem t2285_8 : rows 31 250 ≤ 1107620412346083820 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_8 t2285_9 (by norm_num)

theorem t2285_7 : rows 30 250 ≤ 1109444661268573567 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_7 t2285_8 (by norm_num)

theorem t2285_6 : rows 29 250 ≤ 1111336461386850275 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_6 t2285_7 (by norm_num)

theorem t2285_5 : rows 28 250 ≤ 1113292479488655804 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_5 t2285_6 (by norm_num)

theorem t2285_4 : rows 27 250 ≤ 1115303246253962593 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_4 t2285_5 (by norm_num)

theorem t2285_3 : rows 25 250 ≤ 1119424379650601116 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_3 t2285_4 (by norm_num)

theorem t2285_2 : rows 23 250 ≤ 1123519312646177992 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_2 t2285_3 (by norm_num)

theorem t2285_1 : rows 19 250 ≤ 1130726649020957024 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_1 t2285_2 (by norm_num)

theorem t2285_0 : rows 0 250 ≤ 1140606971340984424 :=
  rows_le_of_split (by norm_num) (by norm_num) rows2285U_0 t2285_1 (by norm_num)

/-- **The certificate on `grid2285U`**: the loss's bound is less than `K`, the 252 parts checked by the kernel. -/
theorem total_lt_2285U : total < K := by
  rw [total_eq_rows_full]
  exact lt_of_le_of_lt t2285_0 (by decide +kernel)

end

end SieveCert

#print axioms SieveCert.total_lt_2285U
