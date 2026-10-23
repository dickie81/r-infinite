/-
# Round 705: the refined certificate of the sieve route's loss at `L = 9/4` with `n = 200`: `total2 < K`

On `SieveGrid225R.grid225R` (`U1 = ⌈(41191/100000)DEN⌉`, `U2 = ⌊(48127/100000)DEN⌋`, `n = 200`), `SieveCert.total2`
is less than `K` (it is below `0.97204K`, rounded up; the certificate of `SieveCertDefs.lean` on the same grid
totals `1.07689K`): `total2` is `rows2 0 n` (`SieveCert2.total2_eq_rows2_full`), and its bound is assembled one step
at a time from the 117 parts' bounds (`rows225R_0` … `rows225R_116`, each by `decide +kernel` in one of the 27 part
files): a heavy row's bound from its column pieces' (`rowsJ2_le_of_split`, `rows2_le_of_rowsJ2`), then the 84 ranges
of rows from the last to the first (`rows2_le_of_split`), every bound a literal and every step a theorem of its own
(`c225R_…`, `hr225R_…`, `t225R_…`); the bounds, `⌈1.001 × part⌉` computed exactly in integers, sum to
`1121795677522305687`, less than `K` by `decide +kernel` (`total2_lt_225R`).

The file imports `SieveCert2.lean` and `SieveCert225RP1.lean` … `SieveCert225RP27.lean`.
-/
import SieveCert2
import SieveCert225RP1
import SieveCert225RP2
import SieveCert225RP3
import SieveCert225RP4
import SieveCert225RP5
import SieveCert225RP6
import SieveCert225RP7
import SieveCert225RP8
import SieveCert225RP9
import SieveCert225RP10
import SieveCert225RP11
import SieveCert225RP12
import SieveCert225RP13
import SieveCert225RP14
import SieveCert225RP15
import SieveCert225RP16
import SieveCert225RP17
import SieveCert225RP18
import SieveCert225RP19
import SieveCert225RP20
import SieveCert225RP21
import SieveCert225RP22
import SieveCert225RP23
import SieveCert225RP24
import SieveCert225RP25
import SieveCert225RP26
import SieveCert225RP27

namespace SieveCert

section

attribute [local instance] grid225R

/-! The chain of bounds: `c225R_{i}_{m}` for the heavy row `i` from its `m`-th column piece on, `hr225R_{i}` for
the heavy row `i`, `t225R_{m}` for the rows from the `m`-th range on; each a theorem of its own, its name distinct
from round 625's chain in the same namespace. -/

theorem c225R_46_0 : rowsJ2 46 47 0 200 ≤ 2710852337218252 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows225R_23 rows225R_24 (by norm_num)

theorem hr225R_46 : rows2 46 47 ≤ 2710852337218252 := rows2_le_of_rowsJ2 46 47 c225R_46_0

theorem c225R_47_0 : rowsJ2 47 48 0 200 ≤ 2565279052202703 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows225R_25 rows225R_26 (by norm_num)

theorem hr225R_47 : rows2 47 48 ≤ 2565279052202703 := rows2_le_of_rowsJ2 47 48 c225R_47_0

theorem c225R_48_0 : rowsJ2 48 49 0 200 ≤ 2432043902925279 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows225R_27 rows225R_28 (by norm_num)

theorem hr225R_48 : rows2 48 49 ≤ 2432043902925279 := rows2_le_of_rowsJ2 48 49 c225R_48_0

theorem c225R_49_0 : rowsJ2 49 50 0 200 ≤ 2294762598926091 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows225R_29 rows225R_30 (by norm_num)

theorem hr225R_49 : rows2 49 50 ≤ 2294762598926091 := rows2_le_of_rowsJ2 49 50 c225R_49_0

theorem c225R_50_0 : rowsJ2 50 51 0 200 ≤ 2167336363509309 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows225R_31 rows225R_32 (by norm_num)

theorem hr225R_50 : rows2 50 51 ≤ 2167336363509309 := rows2_le_of_rowsJ2 50 51 c225R_50_0

theorem c225R_51_0 : rowsJ2 51 52 0 200 ≤ 2033317301172619 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows225R_33 rows225R_34 (by norm_num)

theorem hr225R_51 : rows2 51 52 ≤ 2033317301172619 := rows2_le_of_rowsJ2 51 52 c225R_51_0

theorem c225R_52_0 : rowsJ2 52 53 0 200 ≤ 1914071916832391 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows225R_35 rows225R_36 (by norm_num)

theorem hr225R_52 : rows2 52 53 ≤ 1914071916832391 := rows2_le_of_rowsJ2 52 53 c225R_52_0

theorem c225R_53_0 : rowsJ2 53 54 0 200 ≤ 1793726984956132 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows225R_37 rows225R_38 (by norm_num)

theorem hr225R_53 : rows2 53 54 ≤ 1793726984956132 := rows2_le_of_rowsJ2 53 54 c225R_53_0

theorem c225R_54_0 : rowsJ2 54 55 0 200 ≤ 1693524054841681 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows225R_39 rows225R_40 (by norm_num)

theorem hr225R_54 : rows2 54 55 ≤ 1693524054841681 := rows2_le_of_rowsJ2 54 55 c225R_54_0

theorem c225R_55_0 : rowsJ2 55 56 0 200 ≤ 1599214300094402 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows225R_41 rows225R_42 (by norm_num)

theorem hr225R_55 : rows2 55 56 ≤ 1599214300094402 := rows2_le_of_rowsJ2 55 56 c225R_55_0

theorem c225R_56_0 : rowsJ2 56 57 0 200 ≤ 1530802330154655 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows225R_43 rows225R_44 (by norm_num)

theorem hr225R_56 : rows2 56 57 ≤ 1530802330154655 := rows2_le_of_rowsJ2 56 57 c225R_56_0

theorem c225R_57_0 : rowsJ2 57 58 0 200 ≤ 1470556325850278 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows225R_45 rows225R_46 (by norm_num)

theorem hr225R_57 : rows2 57 58 ≤ 1470556325850278 := rows2_le_of_rowsJ2 57 58 c225R_57_0

theorem c225R_58_0 : rowsJ2 58 59 0 200 ≤ 1819290434009515 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows225R_47 rows225R_48 (by norm_num)

theorem hr225R_58 : rows2 58 59 ≤ 1819290434009515 := rows2_le_of_rowsJ2 58 59 c225R_58_0

theorem c225R_59_0 : rowsJ2 59 60 0 200 ≤ 2041722375639839 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows225R_49 rows225R_50 (by norm_num)

theorem hr225R_59 : rows2 59 60 ≤ 2041722375639839 := rows2_le_of_rowsJ2 59 60 c225R_59_0

theorem c225R_60_0 : rowsJ2 60 61 0 200 ≤ 2527557229440565 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows225R_51 rows225R_52 (by norm_num)

theorem hr225R_60 : rows2 60 61 ≤ 2527557229440565 := rows2_le_of_rowsJ2 60 61 c225R_60_0

theorem c225R_61_0 : rowsJ2 61 62 0 200 ≤ 2714522538228529 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows225R_53 rows225R_54 (by norm_num)

theorem hr225R_61 : rows2 61 62 ≤ 2714522538228529 := rows2_le_of_rowsJ2 61 62 c225R_61_0

theorem c225R_62_0 : rowsJ2 62 63 0 200 ≤ 3157247568412482 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows225R_55 rows225R_56 (by norm_num)

theorem hr225R_62 : rows2 62 63 ≤ 3157247568412482 := rows2_le_of_rowsJ2 62 63 c225R_62_0

theorem c225R_63_0 : rowsJ2 63 64 0 200 ≤ 3308511764022901 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows225R_57 rows225R_58 (by norm_num)

theorem hr225R_63 : rows2 63 64 ≤ 3308511764022901 := rows2_le_of_rowsJ2 63 64 c225R_63_0

theorem c225R_64_0 : rowsJ2 64 65 0 200 ≤ 3122111403163993 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows225R_59 rows225R_60 (by norm_num)

theorem hr225R_64 : rows2 64 65 ≤ 3122111403163993 := rows2_le_of_rowsJ2 64 65 c225R_64_0

theorem c225R_65_0 : rowsJ2 65 66 0 200 ≤ 2778516313686478 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows225R_61 rows225R_62 (by norm_num)

theorem hr225R_65 : rows2 65 66 ≤ 2778516313686478 := rows2_le_of_rowsJ2 65 66 c225R_65_0

theorem c225R_66_0 : rowsJ2 66 67 0 200 ≤ 2701614508075993 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows225R_63 rows225R_64 (by norm_num)

theorem hr225R_66 : rows2 66 67 ≤ 2701614508075993 := rows2_le_of_rowsJ2 66 67 c225R_66_0

theorem c225R_67_0 : rowsJ2 67 68 0 200 ≤ 2377570864709833 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows225R_65 rows225R_66 (by norm_num)

theorem hr225R_67 : rows2 67 68 ≤ 2377570864709833 := rows2_le_of_rowsJ2 67 68 c225R_67_0

theorem c225R_68_0 : rowsJ2 68 69 0 200 ≤ 2313953471987855 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows225R_67 rows225R_68 (by norm_num)

theorem hr225R_68 : rows2 68 69 ≤ 2313953471987855 := rows2_le_of_rowsJ2 68 69 c225R_68_0

theorem c225R_69_0 : rowsJ2 69 70 0 200 ≤ 2009444581561761 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows225R_69 rows225R_70 (by norm_num)

theorem hr225R_69 : rows2 69 70 ≤ 2009444581561761 := rows2_le_of_rowsJ2 69 70 c225R_69_0

theorem c225R_70_0 : rowsJ2 70 71 0 200 ≤ 1961524366592882 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows225R_71 rows225R_72 (by norm_num)

theorem hr225R_70 : rows2 70 71 ≤ 1961524366592882 := rows2_le_of_rowsJ2 70 71 c225R_70_0

theorem c225R_71_0 : rowsJ2 71 72 0 200 ≤ 1675768789633189 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows225R_73 rows225R_74 (by norm_num)

theorem hr225R_71 : rows2 71 72 ≤ 1675768789633189 := rows2_le_of_rowsJ2 71 72 c225R_71_0

theorem c225R_72_0 : rowsJ2 72 73 0 200 ≤ 1645243554793240 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows225R_75 rows225R_76 (by norm_num)

theorem hr225R_72 : rows2 72 73 ≤ 1645243554793240 := rows2_le_of_rowsJ2 72 73 c225R_72_0

theorem c225R_73_0 : rowsJ2 73 74 0 200 ≤ 1371675128043428 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows225R_77 rows225R_78 (by norm_num)

theorem hr225R_73 : rows2 73 74 ≤ 1371675128043428 := rows2_le_of_rowsJ2 73 74 c225R_73_0

theorem c225R_74_0 : rowsJ2 74 75 0 200 ≤ 1343331454291064 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows225R_79 rows225R_80 (by norm_num)

theorem hr225R_74 : rows2 74 75 ≤ 1343331454291064 := rows2_le_of_rowsJ2 74 75 c225R_74_0

theorem c225R_75_0 : rowsJ2 75 76 0 200 ≤ 1067617210528999 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows225R_81 rows225R_82 (by norm_num)

theorem hr225R_75 : rows2 75 76 ≤ 1067617210528999 := rows2_le_of_rowsJ2 75 76 c225R_75_0

theorem c225R_76_0 : rowsJ2 76 77 0 200 ≤ 1039386660424179 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows225R_83 rows225R_84 (by norm_num)

theorem hr225R_76 : rows2 76 77 ≤ 1039386660424179 := rows2_le_of_rowsJ2 76 77 c225R_76_0

theorem c225R_77_0 : rowsJ2 77 78 0 200 ≤ 762637246698147 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows225R_85 rows225R_86 (by norm_num)

theorem hr225R_77 : rows2 77 78 ≤ 762637246698147 := rows2_le_of_rowsJ2 77 78 c225R_77_0

theorem c225R_78_0 : rowsJ2 78 79 0 200 ≤ 735867377997090 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows225R_87 rows225R_88 (by norm_num)

theorem hr225R_78 : rows2 78 79 ≤ 735867377997090 := rows2_le_of_rowsJ2 78 79 c225R_78_0

theorem t225R_82 : rows2 157 200 ≤ 235874997065253463 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_115 rows225R_116 (by norm_num)

theorem t225R_81 : rows2 148 200 ≤ 379379580739749487 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_114 t225R_82 (by norm_num)

theorem t225R_80 : rows2 141 200 ≤ 487356192494639280 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_113 t225R_81 (by norm_num)

theorem t225R_79 : rows2 133 200 ≤ 596821998242051943 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_112 t225R_80 (by norm_num)

theorem t225R_78 : rows2 124 200 ≤ 700451655619594390 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_111 t225R_79 (by norm_num)

theorem t225R_77 : rows2 114 200 ≤ 792009188702951900 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_110 t225R_78 (by norm_num)

theorem t225R_76 : rows2 108 200 ≤ 831845368100359759 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_109 t225R_77 (by norm_num)

theorem t225R_75 : rows2 104 200 ≤ 852137689780878223 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_108 t225R_76 (by norm_num)

theorem t225R_74 : rows2 101 200 ≤ 864619190257071013 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_107 t225R_75 (by norm_num)

theorem t225R_73 : rows2 99 200 ≤ 872759636682785670 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_106 t225R_74 (by norm_num)

theorem t225R_72 : rows2 97 200 ≤ 880797993918097748 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_105 t225R_73 (by norm_num)

theorem t225R_71 : rows2 95 200 ≤ 888733032710826631 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_104 t225R_72 (by norm_num)

theorem t225R_70 : rows2 93 200 ≤ 896595267102562349 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_103 t225R_71 (by norm_num)

theorem t225R_69 : rows2 92 200 ≤ 900524472972490849 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_102 t225R_70 (by norm_num)

theorem t225R_68 : rows2 91 200 ≤ 904438898104652407 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_101 t225R_69 (by norm_num)

theorem t225R_67 : rows2 90 200 ≤ 908350619982679890 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_100 t225R_68 (by norm_num)

theorem t225R_66 : rows2 89 200 ≤ 912274586878238865 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_99 t225R_67 (by norm_num)

theorem t225R_65 : rows2 88 200 ≤ 916205331021108520 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_98 t225R_66 (by norm_num)

theorem t225R_64 : rows2 87 200 ≤ 919798233093746797 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_97 t225R_65 (by norm_num)

theorem t225R_63 : rows2 86 200 ≤ 923083034562691049 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_96 t225R_64 (by norm_num)

theorem t225R_62 : rows2 85 200 ≤ 926024960829806233 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_95 t225R_63 (by norm_num)

theorem t225R_61 : rows2 84 200 ≤ 928628933567955519 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_94 t225R_62 (by norm_num)

theorem t225R_60 : rows2 83 200 ≤ 930879719351157530 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_93 t225R_61 (by norm_num)

theorem t225R_59 : rows2 82 200 ≤ 932758385050365289 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_92 t225R_60 (by norm_num)

theorem t225R_58 : rows2 81 200 ≤ 934243250966100283 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_91 t225R_59 (by norm_num)

theorem t225R_57 : rows2 80 200 ≤ 935334432377354605 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_90 t225R_58 (by norm_num)

theorem t225R_56 : rows2 79 200 ≤ 936014387440319046 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_89 t225R_57 (by norm_num)

theorem t225R_55 : rows2 78 200 ≤ 936750254818316136 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_78 t225R_56 (by norm_num)

theorem t225R_54 : rows2 77 200 ≤ 937512892065014283 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_77 t225R_55 (by norm_num)

theorem t225R_53 : rows2 76 200 ≤ 938552278725438462 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_76 t225R_54 (by norm_num)

theorem t225R_52 : rows2 75 200 ≤ 939619895935967461 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_75 t225R_53 (by norm_num)

theorem t225R_51 : rows2 74 200 ≤ 940963227390258525 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_74 t225R_52 (by norm_num)

theorem t225R_50 : rows2 73 200 ≤ 942334902518301953 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_73 t225R_51 (by norm_num)

theorem t225R_49 : rows2 72 200 ≤ 943980146073095193 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_72 t225R_50 (by norm_num)

theorem t225R_48 : rows2 71 200 ≤ 945655914862728382 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_71 t225R_49 (by norm_num)

theorem t225R_47 : rows2 70 200 ≤ 947617439229321264 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_70 t225R_48 (by norm_num)

theorem t225R_46 : rows2 69 200 ≤ 949626883810883025 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_69 t225R_47 (by norm_num)

theorem t225R_45 : rows2 68 200 ≤ 951940837282870880 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_68 t225R_46 (by norm_num)

theorem t225R_44 : rows2 67 200 ≤ 954318408147580713 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_67 t225R_45 (by norm_num)

theorem t225R_43 : rows2 66 200 ≤ 957020022655656706 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_66 t225R_44 (by norm_num)

theorem t225R_42 : rows2 65 200 ≤ 959798538969343184 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_65 t225R_43 (by norm_num)

theorem t225R_41 : rows2 64 200 ≤ 962920650372507177 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_64 t225R_42 (by norm_num)

theorem t225R_40 : rows2 63 200 ≤ 966229162136530078 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_63 t225R_41 (by norm_num)

theorem t225R_39 : rows2 62 200 ≤ 969386409704942560 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_62 t225R_40 (by norm_num)

theorem t225R_38 : rows2 61 200 ≤ 972100932243171089 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_61 t225R_39 (by norm_num)

theorem t225R_37 : rows2 60 200 ≤ 974628489472611654 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_60 t225R_38 (by norm_num)

theorem t225R_36 : rows2 59 200 ≤ 976670211848251493 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_59 t225R_37 (by norm_num)

theorem t225R_35 : rows2 58 200 ≤ 978489502282261008 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_58 t225R_36 (by norm_num)

theorem t225R_34 : rows2 57 200 ≤ 979960058608111286 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_57 t225R_35 (by norm_num)

theorem t225R_33 : rows2 56 200 ≤ 981490860938265941 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_56 t225R_34 (by norm_num)

theorem t225R_32 : rows2 55 200 ≤ 983090075238360343 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_55 t225R_33 (by norm_num)

theorem t225R_31 : rows2 54 200 ≤ 984783599293202024 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_54 t225R_32 (by norm_num)

theorem t225R_30 : rows2 53 200 ≤ 986577326278158156 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_53 t225R_31 (by norm_num)

theorem t225R_29 : rows2 52 200 ≤ 988491398194990547 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_52 t225R_30 (by norm_num)

theorem t225R_28 : rows2 51 200 ≤ 990524715496163166 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_51 t225R_29 (by norm_num)

theorem t225R_27 : rows2 50 200 ≤ 992692051859672475 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_50 t225R_28 (by norm_num)

theorem t225R_26 : rows2 49 200 ≤ 994986814458598566 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_49 t225R_27 (by norm_num)

theorem t225R_25 : rows2 48 200 ≤ 997418858361523845 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_48 t225R_26 (by norm_num)

theorem t225R_24 : rows2 47 200 ≤ 999984137413726548 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_47 t225R_25 (by norm_num)

theorem t225R_23 : rows2 46 200 ≤ 1002694989750944800 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr225R_46 t225R_24 (by norm_num)

theorem t225R_22 : rows2 45 200 ≤ 1005540450252542957 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_22 t225R_23 (by norm_num)

theorem t225R_21 : rows2 44 200 ≤ 1008520570508522494 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_21 t225R_22 (by norm_num)

theorem t225R_20 : rows2 43 200 ≤ 1011617306866779774 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_20 t225R_21 (by norm_num)

theorem t225R_19 : rows2 42 200 ≤ 1014825555218876038 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_19 t225R_20 (by norm_num)

theorem t225R_18 : rows2 41 200 ≤ 1018125510901134071 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_18 t225R_19 (by norm_num)

theorem t225R_17 : rows2 40 200 ≤ 1021509355447281571 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_17 t225R_18 (by norm_num)

theorem t225R_16 : rows2 39 200 ≤ 1024953997880810699 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_16 t225R_17 (by norm_num)

theorem t225R_15 : rows2 38 200 ≤ 1028451450061720926 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_15 t225R_16 (by norm_num)

theorem t225R_14 : rows2 37 200 ≤ 1031978521990749710 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_14 t225R_15 (by norm_num)

theorem t225R_13 : rows2 36 200 ≤ 1035527816740093714 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_13 t225R_14 (by norm_num)

theorem t225R_12 : rows2 35 200 ≤ 1039080268506080008 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_12 t225R_13 (by norm_num)

theorem t225R_11 : rows2 34 200 ≤ 1042631048120636709 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_11 t225R_12 (by norm_num)

theorem t225R_10 : rows2 33 200 ≤ 1046162333444326118 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_10 t225R_11 (by norm_num)

theorem t225R_9 : rows2 32 200 ≤ 1049672422180868297 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_9 t225R_10 (by norm_num)

theorem t225R_8 : rows2 31 200 ≤ 1053145324886099703 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_8 t225R_9 (by norm_num)

theorem t225R_7 : rows2 30 200 ≤ 1056601740590435516 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_7 t225R_8 (by norm_num)

theorem t225R_6 : rows2 29 200 ≤ 1060088955603250718 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_6 t225R_7 (by norm_num)

theorem t225R_5 : rows2 28 200 ≤ 1063643615016069607 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_5 t225R_6 (by norm_num)

theorem t225R_4 : rows2 27 200 ≤ 1067288555799439947 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_4 t225R_5 (by norm_num)

theorem t225R_3 : rows2 25 200 ≤ 1074879552969117456 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_3 t225R_4 (by norm_num)

theorem t225R_2 : rows2 23 200 ≤ 1082772326361052936 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_2 t225R_3 (by norm_num)

theorem t225R_1 : rows2 19 200 ≤ 1098026294017315840 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_1 t225R_2 (by norm_num)

theorem t225R_0 : rows2 0 200 ≤ 1121795677522305687 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows225R_0 t225R_1 (by norm_num)

/-- **The refined certificate on `grid225R`**: the loss's bound is less than `K`, the 117 parts checked by the
kernel. -/
theorem total2_lt_225R : total2 < K := by
  rw [total2_eq_rows2_full]
  exact lt_of_le_of_lt t225R_0 (by decide +kernel)

end

end SieveCert

#print axioms SieveCert.total2_lt_225R
