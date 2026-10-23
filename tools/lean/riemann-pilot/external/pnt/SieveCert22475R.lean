/-
# Round 710: the refined certificate of the sieve route's loss at `L = 899/400` with `n = 300`: `total2 < K`

On `SieveGrid22475R.grid22475R` (`U1 = ⌈(41335/100000)DEN⌉`, `U2 = ⌊(48069/100000)DEN⌋`, `n = 300`),
`SieveCert.total2` is less than `K` (it is below `0.99386K`, rounded up; the certificate of `SieveCertDefs.lean` on
the same grid totals `1.10458K`): `total2` is `rows2 0 n` (`SieveCert2.total2_eq_rows2_full`), and its bound is
assembled one step at a time from the 534 parts' bounds (`rows22475R_0` … `rows22475R_533`, each by `decide +kernel`
in one of the 135 part files): a heavy row's bound from its column pieces' (`rowsJ2_le_of_split`,
`rows2_le_of_rowsJ2`), then the 171 ranges of rows from the last to the first (`rows2_le_of_split`), every bound a
literal and every step a theorem of its own (`c22475R_…`, `hr22475R_…`, `t22475R_…`); the bounds, `⌈1.001 × part⌉`
computed exactly in integers, sum to `1146984490308086981`, less than `K` by `decide +kernel` (`total2_lt_22475R`).

The file imports `SieveCert2.lean` and `SieveCert22475RP1.lean` … `SieveCert22475RP135.lean`.
-/
import SieveCert2
import SieveCert22475RP1
import SieveCert22475RP2
import SieveCert22475RP3
import SieveCert22475RP4
import SieveCert22475RP5
import SieveCert22475RP6
import SieveCert22475RP7
import SieveCert22475RP8
import SieveCert22475RP9
import SieveCert22475RP10
import SieveCert22475RP11
import SieveCert22475RP12
import SieveCert22475RP13
import SieveCert22475RP14
import SieveCert22475RP15
import SieveCert22475RP16
import SieveCert22475RP17
import SieveCert22475RP18
import SieveCert22475RP19
import SieveCert22475RP20
import SieveCert22475RP21
import SieveCert22475RP22
import SieveCert22475RP23
import SieveCert22475RP24
import SieveCert22475RP25
import SieveCert22475RP26
import SieveCert22475RP27
import SieveCert22475RP28
import SieveCert22475RP29
import SieveCert22475RP30
import SieveCert22475RP31
import SieveCert22475RP32
import SieveCert22475RP33
import SieveCert22475RP34
import SieveCert22475RP35
import SieveCert22475RP36
import SieveCert22475RP37
import SieveCert22475RP38
import SieveCert22475RP39
import SieveCert22475RP40
import SieveCert22475RP41
import SieveCert22475RP42
import SieveCert22475RP43
import SieveCert22475RP44
import SieveCert22475RP45
import SieveCert22475RP46
import SieveCert22475RP47
import SieveCert22475RP48
import SieveCert22475RP49
import SieveCert22475RP50
import SieveCert22475RP51
import SieveCert22475RP52
import SieveCert22475RP53
import SieveCert22475RP54
import SieveCert22475RP55
import SieveCert22475RP56
import SieveCert22475RP57
import SieveCert22475RP58
import SieveCert22475RP59
import SieveCert22475RP60
import SieveCert22475RP61
import SieveCert22475RP62
import SieveCert22475RP63
import SieveCert22475RP64
import SieveCert22475RP65
import SieveCert22475RP66
import SieveCert22475RP67
import SieveCert22475RP68
import SieveCert22475RP69
import SieveCert22475RP70
import SieveCert22475RP71
import SieveCert22475RP72
import SieveCert22475RP73
import SieveCert22475RP74
import SieveCert22475RP75
import SieveCert22475RP76
import SieveCert22475RP77
import SieveCert22475RP78
import SieveCert22475RP79
import SieveCert22475RP80
import SieveCert22475RP81
import SieveCert22475RP82
import SieveCert22475RP83
import SieveCert22475RP84
import SieveCert22475RP85
import SieveCert22475RP86
import SieveCert22475RP87
import SieveCert22475RP88
import SieveCert22475RP89
import SieveCert22475RP90
import SieveCert22475RP91
import SieveCert22475RP92
import SieveCert22475RP93
import SieveCert22475RP94
import SieveCert22475RP95
import SieveCert22475RP96
import SieveCert22475RP97
import SieveCert22475RP98
import SieveCert22475RP99
import SieveCert22475RP100
import SieveCert22475RP101
import SieveCert22475RP102
import SieveCert22475RP103
import SieveCert22475RP104
import SieveCert22475RP105
import SieveCert22475RP106
import SieveCert22475RP107
import SieveCert22475RP108
import SieveCert22475RP109
import SieveCert22475RP110
import SieveCert22475RP111
import SieveCert22475RP112
import SieveCert22475RP113
import SieveCert22475RP114
import SieveCert22475RP115
import SieveCert22475RP116
import SieveCert22475RP117
import SieveCert22475RP118
import SieveCert22475RP119
import SieveCert22475RP120
import SieveCert22475RP121
import SieveCert22475RP122
import SieveCert22475RP123
import SieveCert22475RP124
import SieveCert22475RP125
import SieveCert22475RP126
import SieveCert22475RP127
import SieveCert22475RP128
import SieveCert22475RP129
import SieveCert22475RP130
import SieveCert22475RP131
import SieveCert22475RP132
import SieveCert22475RP133
import SieveCert22475RP134
import SieveCert22475RP135

namespace SieveCert

section

attribute [local instance] grid22475R

/-! The chain of bounds: `c22475R_{i}_{m}` for the heavy row `i` from its `m`-th column piece on, `hr22475R_{i}` for
the heavy row `i`, `t22475R_{m}` for the rows from the `m`-th range on; each a theorem of its own, its name distinct
from rounds 625's and 705's chains in the same namespace. -/

theorem c22475R_35_0 : rowsJ2 35 36 0 300 ≤ 3061807096165505 :=
  rowsJ2_le_of_split 35 36 (by norm_num) (by norm_num) rows22475R_12 rows22475R_13 (by norm_num)

theorem hr22475R_35 : rows2 35 36 ≤ 3061807096165505 := rows2_le_of_rowsJ2 35 36 c22475R_35_0

theorem c22475R_36_0 : rowsJ2 36 37 0 300 ≤ 3068854812180277 :=
  rowsJ2_le_of_split 36 37 (by norm_num) (by norm_num) rows22475R_14 rows22475R_15 (by norm_num)

theorem hr22475R_36 : rows2 36 37 ≤ 3068854812180277 := rows2_le_of_rowsJ2 36 37 c22475R_36_0

theorem c22475R_37_0 : rowsJ2 37 38 0 300 ≤ 3059237129442448 :=
  rowsJ2_le_of_split 37 38 (by norm_num) (by norm_num) rows22475R_16 rows22475R_17 (by norm_num)

theorem hr22475R_37 : rows2 37 38 ≤ 3059237129442448 := rows2_le_of_rowsJ2 37 38 c22475R_37_0

theorem c22475R_38_0 : rowsJ2 38 39 0 300 ≤ 3035775677939228 :=
  rowsJ2_le_of_split 38 39 (by norm_num) (by norm_num) rows22475R_18 rows22475R_19 (by norm_num)

theorem hr22475R_38 : rows2 38 39 ≤ 3035775677939228 := rows2_le_of_rowsJ2 38 39 c22475R_38_0

theorem c22475R_39_0 : rowsJ2 39 40 0 300 ≤ 3001310443088200 :=
  rowsJ2_le_of_split 39 40 (by norm_num) (by norm_num) rows22475R_20 rows22475R_21 (by norm_num)

theorem hr22475R_39 : rows2 39 40 ≤ 3001310443088200 := rows2_le_of_rowsJ2 39 40 c22475R_39_0

theorem c22475R_40_0 : rowsJ2 40 41 0 300 ≤ 2958384757168059 :=
  rowsJ2_le_of_split 40 41 (by norm_num) (by norm_num) rows22475R_22 rows22475R_23 (by norm_num)

theorem hr22475R_40 : rows2 40 41 ≤ 2958384757168059 := rows2_le_of_rowsJ2 40 41 c22475R_40_0

theorem c22475R_41_0 : rowsJ2 41 42 0 300 ≤ 2910243483216330 :=
  rowsJ2_le_of_split 41 42 (by norm_num) (by norm_num) rows22475R_24 rows22475R_25 (by norm_num)

theorem hr22475R_41 : rows2 41 42 ≤ 2910243483216330 := rows2_le_of_rowsJ2 41 42 c22475R_41_0

theorem c22475R_42_0 : rowsJ2 42 43 0 300 ≤ 2859370948505308 :=
  rowsJ2_le_of_split 42 43 (by norm_num) (by norm_num) rows22475R_26 rows22475R_27 (by norm_num)

theorem hr22475R_42 : rows2 42 43 ≤ 2859370948505308 := rows2_le_of_rowsJ2 42 43 c22475R_42_0

theorem c22475R_43_0 : rowsJ2 43 44 0 300 ≤ 2808856641982762 :=
  rowsJ2_le_of_split 43 44 (by norm_num) (by norm_num) rows22475R_28 rows22475R_29 (by norm_num)

theorem hr22475R_43 : rows2 43 44 ≤ 2808856641982762 := rows2_le_of_rowsJ2 43 44 c22475R_43_0

theorem c22475R_44_1 : rowsJ2 44 45 35 300 ≤ 511426387773206 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22475R_31 rows22475R_32 (by norm_num)

theorem c22475R_44_0 : rowsJ2 44 45 0 300 ≤ 2761433148591374 :=
  rowsJ2_le_of_split 44 45 (by norm_num) (by norm_num) rows22475R_30 c22475R_44_1 (by norm_num)

theorem hr22475R_44 : rows2 44 45 ≤ 2761433148591374 := rows2_le_of_rowsJ2 44 45 c22475R_44_0

theorem c22475R_45_1 : rowsJ2 45 46 35 300 ≤ 547863631467837 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22475R_34 rows22475R_35 (by norm_num)

theorem c22475R_45_0 : rowsJ2 45 46 0 300 ≤ 2719452659824706 :=
  rowsJ2_le_of_split 45 46 (by norm_num) (by norm_num) rows22475R_33 c22475R_45_1 (by norm_num)

theorem hr22475R_45 : rows2 45 46 ≤ 2719452659824706 := rows2_le_of_rowsJ2 45 46 c22475R_45_0

theorem c22475R_46_1 : rowsJ2 46 47 35 300 ≤ 591994588453226 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22475R_37 rows22475R_38 (by norm_num)

theorem c22475R_46_0 : rowsJ2 46 47 0 300 ≤ 2685203885556050 :=
  rowsJ2_le_of_split 46 47 (by norm_num) (by norm_num) rows22475R_36 c22475R_46_1 (by norm_num)

theorem hr22475R_46 : rows2 46 47 ≤ 2685203885556050 := rows2_le_of_rowsJ2 46 47 c22475R_46_0

theorem c22475R_47_1 : rowsJ2 47 48 35 300 ≤ 646157825599949 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22475R_40 rows22475R_41 (by norm_num)

theorem c22475R_47_0 : rowsJ2 47 48 0 300 ≤ 2661793166144080 :=
  rowsJ2_le_of_split 47 48 (by norm_num) (by norm_num) rows22475R_39 c22475R_47_1 (by norm_num)

theorem hr22475R_47 : rows2 47 48 ≤ 2661793166144080 := rows2_le_of_rowsJ2 47 48 c22475R_47_0

theorem c22475R_48_1 : rowsJ2 48 49 35 300 ≤ 713136148168166 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22475R_43 rows22475R_44 (by norm_num)

theorem c22475R_48_0 : rowsJ2 48 49 0 300 ≤ 2651479866904599 :=
  rowsJ2_le_of_split 48 49 (by norm_num) (by norm_num) rows22475R_42 c22475R_48_1 (by norm_num)

theorem hr22475R_48 : rows2 48 49 ≤ 2651479866904599 := rows2_le_of_rowsJ2 48 49 c22475R_48_0

theorem c22475R_49_1 : rowsJ2 49 50 35 300 ≤ 789093202901150 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22475R_46 rows22475R_47 (by norm_num)

theorem c22475R_49_0 : rowsJ2 49 50 0 300 ≤ 2650928511142384 :=
  rowsJ2_le_of_split 49 50 (by norm_num) (by norm_num) rows22475R_45 c22475R_49_1 (by norm_num)

theorem hr22475R_49 : rows2 49 50 ≤ 2650928511142384 := rows2_le_of_rowsJ2 49 50 c22475R_49_0

theorem c22475R_50_1 : rowsJ2 50 51 35 300 ≤ 862370751399545 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22475R_49 rows22475R_50 (by norm_num)

theorem c22475R_50_0 : rowsJ2 50 51 0 300 ≤ 2648368035342243 :=
  rowsJ2_le_of_split 50 51 (by norm_num) (by norm_num) rows22475R_48 c22475R_50_1 (by norm_num)

theorem hr22475R_50 : rows2 50 51 ≤ 2648368035342243 := rows2_le_of_rowsJ2 50 51 c22475R_50_0

theorem c22475R_51_2 : rowsJ2 51 52 44 300 ≤ 576178801538000 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22475R_53 rows22475R_54 (by norm_num)

theorem c22475R_51_1 : rowsJ2 51 52 35 300 ≤ 930251673187946 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22475R_52 c22475R_51_2 (by norm_num)

theorem c22475R_51_0 : rowsJ2 51 52 0 300 ≤ 2641469769991443 :=
  rowsJ2_le_of_split 51 52 (by norm_num) (by norm_num) rows22475R_51 c22475R_51_1 (by norm_num)

theorem hr22475R_51 : rows2 51 52 ≤ 2641469769991443 := rows2_le_of_rowsJ2 51 52 c22475R_51_0

theorem c22475R_52_2 : rowsJ2 52 53 44 300 ≤ 647323796938597 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22475R_57 rows22475R_58 (by norm_num)

theorem c22475R_52_1 : rowsJ2 52 53 35 300 ≤ 997310709167880 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22475R_56 c22475R_52_2 (by norm_num)

theorem c22475R_52_0 : rowsJ2 52 53 0 300 ≤ 2634404817498137 :=
  rowsJ2_le_of_split 52 53 (by norm_num) (by norm_num) rows22475R_55 c22475R_52_1 (by norm_num)

theorem hr22475R_52 : rows2 52 53 ≤ 2634404817498137 := rows2_le_of_rowsJ2 52 53 c22475R_52_0

theorem c22475R_53_2 : rowsJ2 53 54 44 300 ≤ 710629365047779 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22475R_61 rows22475R_62 (by norm_num)

theorem c22475R_53_1 : rowsJ2 53 54 35 300 ≤ 1058879809252877 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22475R_60 c22475R_53_2 (by norm_num)

theorem c22475R_53_0 : rowsJ2 53 54 0 300 ≤ 2623334924244963 :=
  rowsJ2_le_of_split 53 54 (by norm_num) (by norm_num) rows22475R_59 c22475R_53_1 (by norm_num)

theorem hr22475R_53 : rows2 53 54 ≤ 2623334924244963 := rows2_le_of_rowsJ2 53 54 c22475R_53_0

theorem c22475R_54_2 : rowsJ2 54 55 44 300 ≤ 769477612054393 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22475R_65 rows22475R_66 (by norm_num)

theorem c22475R_54_1 : rowsJ2 54 55 35 300 ≤ 1118948318622412 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22475R_64 c22475R_54_2 (by norm_num)

theorem c22475R_54_0 : rowsJ2 54 55 0 300 ≤ 2611714372731605 :=
  rowsJ2_le_of_split 54 55 (by norm_num) (by norm_num) rows22475R_63 c22475R_54_1 (by norm_num)

theorem hr22475R_54 : rows2 54 55 ≤ 2611714372731605 := rows2_le_of_rowsJ2 54 55 c22475R_54_0

theorem c22475R_55_2 : rowsJ2 55 56 44 300 ≤ 819732734854691 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22475R_69 rows22475R_70 (by norm_num)

theorem c22475R_55_1 : rowsJ2 55 56 35 300 ≤ 1172875643133595 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22475R_68 c22475R_55_2 (by norm_num)

theorem c22475R_55_0 : rowsJ2 55 56 0 300 ≤ 2595452579163089 :=
  rowsJ2_le_of_split 55 56 (by norm_num) (by norm_num) rows22475R_67 c22475R_55_1 (by norm_num)

theorem hr22475R_55 : rows2 55 56 ≤ 2595452579163089 := rows2_le_of_rowsJ2 55 56 c22475R_55_0

theorem c22475R_56_2 : rowsJ2 56 57 44 300 ≤ 864717777956002 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22475R_73 rows22475R_74 (by norm_num)

theorem c22475R_56_1 : rowsJ2 56 57 35 300 ≤ 1224623557318757 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22475R_72 c22475R_56_2 (by norm_num)

theorem c22475R_56_0 : rowsJ2 56 57 0 300 ≤ 2578412659067798 :=
  rowsJ2_le_of_split 56 57 (by norm_num) (by norm_num) rows22475R_71 c22475R_56_1 (by norm_num)

theorem hr22475R_56 : rows2 56 57 ≤ 2578412659067798 := rows2_le_of_rowsJ2 56 57 c22475R_56_0

theorem c22475R_57_2 : rowsJ2 57 58 44 300 ≤ 900244989827457 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22475R_77 rows22475R_78 (by norm_num)

theorem c22475R_57_1 : rowsJ2 57 58 35 300 ≤ 1269409646167576 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22475R_76 c22475R_57_2 (by norm_num)

theorem c22475R_57_0 : rowsJ2 57 58 0 300 ≤ 2556250434474273 :=
  rowsJ2_le_of_split 57 58 (by norm_num) (by norm_num) rows22475R_75 c22475R_57_1 (by norm_num)

theorem hr22475R_57 : rows2 57 58 ≤ 2556250434474273 := rows2_le_of_rowsJ2 57 58 c22475R_57_0

theorem c22475R_58_2 : rowsJ2 58 59 44 300 ≤ 929829709786160 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22475R_81 rows22475R_82 (by norm_num)

theorem c22475R_58_1 : rowsJ2 58 59 35 300 ≤ 1311245045733355 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22475R_80 c22475R_58_2 (by norm_num)

theorem c22475R_58_0 : rowsJ2 58 59 0 300 ≤ 2532568766854520 :=
  rowsJ2_le_of_split 58 59 (by norm_num) (by norm_num) rows22475R_79 c22475R_58_1 (by norm_num)

theorem hr22475R_58 : rows2 58 59 ≤ 2532568766854520 := rows2_le_of_rowsJ2 58 59 c22475R_58_0

theorem c22475R_59_2 : rowsJ2 59 60 44 300 ≤ 949228646898519 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22475R_85 rows22475R_86 (by norm_num)

theorem c22475R_59_1 : rowsJ2 59 60 35 300 ≤ 1345274293149177 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22475R_84 c22475R_59_2 (by norm_num)

theorem c22475R_59_0 : rowsJ2 59 60 0 300 ≤ 2503425348434133 :=
  rowsJ2_le_of_split 59 60 (by norm_num) (by norm_num) rows22475R_83 c22475R_59_1 (by norm_num)

theorem hr22475R_59 : rows2 59 60 ≤ 2503425348434133 := rows2_le_of_rowsJ2 59 60 c22475R_59_0

theorem c22475R_60_2 : rowsJ2 60 61 44 300 ≤ 962399626354628 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22475R_89 rows22475R_90 (by norm_num)

theorem c22475R_60_1 : rowsJ2 60 61 35 300 ≤ 1375390164833343 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22475R_88 c22475R_60_2 (by norm_num)

theorem c22475R_60_0 : rowsJ2 60 61 0 300 ≤ 2472169038700089 :=
  rowsJ2_le_of_split 60 61 (by norm_num) (by norm_num) rows22475R_87 c22475R_60_1 (by norm_num)

theorem hr22475R_60 : rows2 60 61 ≤ 2472169038700089 := rows2_le_of_rowsJ2 60 61 c22475R_60_0

theorem c22475R_61_2 : rowsJ2 61 62 44 300 ≤ 969322641863610 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22475R_93 rows22475R_94 (by norm_num)

theorem c22475R_61_1 : rowsJ2 61 62 35 300 ≤ 1396836784527719 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22475R_92 c22475R_61_2 (by norm_num)

theorem c22475R_61_0 : rowsJ2 61 62 0 300 ≤ 2434662453995972 :=
  rowsJ2_le_of_split 61 62 (by norm_num) (by norm_num) rows22475R_91 c22475R_61_1 (by norm_num)

theorem hr22475R_61 : rows2 61 62 ≤ 2434662453995972 := rows2_le_of_rowsJ2 61 62 c22475R_61_0

theorem c22475R_62_2 : rowsJ2 62 63 44 300 ≤ 970028923826238 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22475R_97 rows22475R_98 (by norm_num)

theorem c22475R_62_1 : rowsJ2 62 63 35 300 ≤ 1413894024354858 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22475R_96 c22475R_62_2 (by norm_num)

theorem c22475R_62_0 : rowsJ2 62 63 0 300 ≤ 2395109514162663 :=
  rowsJ2_le_of_split 62 63 (by norm_num) (by norm_num) rows22475R_95 c22475R_62_1 (by norm_num)

theorem hr22475R_62 : rows2 62 63 ≤ 2395109514162663 := rows2_le_of_rowsJ2 62 63 c22475R_62_0

theorem c22475R_63_2 : rowsJ2 63 64 44 300 ≤ 964814758246266 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22475R_101 rows22475R_102 (by norm_num)

theorem c22475R_63_1 : rowsJ2 63 64 35 300 ≤ 1421995122803076 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22475R_100 c22475R_63_2 (by norm_num)

theorem c22475R_63_0 : rowsJ2 63 64 0 300 ≤ 2349451728582318 :=
  rowsJ2_le_of_split 63 64 (by norm_num) (by norm_num) rows22475R_99 c22475R_63_1 (by norm_num)

theorem hr22475R_63 : rows2 63 64 ≤ 2349451728582318 := rows2_le_of_rowsJ2 63 64 c22475R_63_0

theorem c22475R_64_2 : rowsJ2 64 65 45 300 ≤ 889429838166199 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22475R_105 rows22475R_106 (by norm_num)

theorem c22475R_64_1 : rowsJ2 64 65 35 300 ≤ 1425601956589458 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22475R_104 c22475R_64_2 (by norm_num)

theorem c22475R_64_0 : rowsJ2 64 65 0 300 ≤ 2301743676864434 :=
  rowsJ2_le_of_split 64 65 (by norm_num) (by norm_num) rows22475R_103 c22475R_64_1 (by norm_num)

theorem hr22475R_64 : rows2 64 65 ≤ 2301743676864434 := rows2_le_of_rowsJ2 64 65 c22475R_64_0

theorem c22475R_65_2 : rowsJ2 65 66 45 300 ≤ 874708582375768 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22475R_109 rows22475R_110 (by norm_num)

theorem c22475R_65_1 : rowsJ2 65 66 35 300 ≤ 1420275156847457 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22475R_108 c22475R_65_2 (by norm_num)

theorem c22475R_65_0 : rowsJ2 65 66 0 300 ≤ 2248570357102222 :=
  rowsJ2_le_of_split 65 66 (by norm_num) (by norm_num) rows22475R_107 c22475R_65_1 (by norm_num)

theorem hr22475R_65 : rows2 65 66 ≤ 2248570357102222 := rows2_le_of_rowsJ2 65 66 c22475R_65_0

theorem c22475R_66_2 : rowsJ2 66 67 45 300 ≤ 855016371342566 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22475R_113 rows22475R_114 (by norm_num)

theorem c22475R_66_1 : rowsJ2 66 67 35 300 ≤ 1410501003458165 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22475R_112 c22475R_66_2 (by norm_num)

theorem c22475R_66_0 : rowsJ2 66 67 0 300 ≤ 2193871009269378 :=
  rowsJ2_le_of_split 66 67 (by norm_num) (by norm_num) rows22475R_111 c22475R_66_1 (by norm_num)

theorem hr22475R_66 : rows2 66 67 ≤ 2193871009269378 := rows2_le_of_rowsJ2 66 67 c22475R_66_0

theorem c22475R_67_2 : rowsJ2 67 68 45 300 ≤ 830619364862869 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22475R_117 rows22475R_118 (by norm_num)

theorem c22475R_67_1 : rowsJ2 67 68 35 300 ≤ 1391925398769523 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22475R_116 c22475R_67_2 (by norm_num)

theorem c22475R_67_0 : rowsJ2 67 68 0 300 ≤ 2134004832293169 :=
  rowsJ2_le_of_split 67 68 (by norm_num) (by norm_num) rows22475R_115 c22475R_67_1 (by norm_num)

theorem hr22475R_67 : rows2 67 68 ≤ 2134004832293169 := rows2_le_of_rowsJ2 67 68 c22475R_67_0

theorem c22475R_68_2 : rowsJ2 68 69 46 300 ≤ 746431853689327 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22475R_121 rows22475R_122 (by norm_num)

theorem c22475R_68_1 : rowsJ2 68 69 35 300 ≤ 1369117509249745 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22475R_120 c22475R_68_2 (by norm_num)

theorem c22475R_68_0 : rowsJ2 68 69 0 300 ≤ 2073500664274779 :=
  rowsJ2_le_of_split 68 69 (by norm_num) (by norm_num) rows22475R_119 c22475R_68_1 (by norm_num)

theorem hr22475R_68 : rows2 68 69 ≤ 2073500664274779 := rows2_le_of_rowsJ2 68 69 c22475R_68_0

theorem c22475R_69_2 : rowsJ2 69 70 46 300 ≤ 715946372838161 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22475R_125 rows22475R_126 (by norm_num)

theorem c22475R_69_1 : rowsJ2 69 70 35 300 ≤ 1338185272451258 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22475R_124 c22475R_69_2 (by norm_num)

theorem c22475R_69_0 : rowsJ2 69 70 0 300 ≤ 2008552037419014 :=
  rowsJ2_le_of_split 69 70 (by norm_num) (by norm_num) rows22475R_123 c22475R_69_1 (by norm_num)

theorem hr22475R_69 : rows2 69 70 ≤ 2008552037419014 := rows2_le_of_rowsJ2 69 70 c22475R_69_0

theorem c22475R_70_2 : rowsJ2 70 71 47 300 ≤ 632238653563022 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22475R_129 rows22475R_130 (by norm_num)

theorem c22475R_70_1 : rowsJ2 70 71 35 300 ≤ 1303914812513782 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22475R_128 c22475R_70_2 (by norm_num)

theorem c22475R_70_0 : rowsJ2 70 71 0 300 ≤ 1943544003151096 :=
  rowsJ2_le_of_split 70 71 (by norm_num) (by norm_num) rows22475R_127 c22475R_70_1 (by norm_num)

theorem hr22475R_70 : rows2 70 71 ≤ 1943544003151096 := rows2_le_of_rowsJ2 70 71 c22475R_70_0

theorem c22475R_71_2 : rowsJ2 71 72 48 300 ≤ 551868210473092 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22475R_133 rows22475R_134 (by norm_num)

theorem c22475R_71_1 : rowsJ2 71 72 35 300 ≤ 1262625607694909 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22475R_132 c22475R_71_2 (by norm_num)

theorem c22475R_71_0 : rowsJ2 71 72 0 300 ≤ 1875416600406371 :=
  rowsJ2_le_of_split 71 72 (by norm_num) (by norm_num) rows22475R_131 c22475R_71_1 (by norm_num)

theorem hr22475R_71 : rows2 71 72 ≤ 1875416600406371 := rows2_le_of_rowsJ2 71 72 c22475R_71_0

theorem c22475R_72_2 : rowsJ2 72 73 49 300 ≤ 475891834550982 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22475R_137 rows22475R_138 (by norm_num)

theorem c22475R_72_1 : rowsJ2 72 73 35 300 ≤ 1219444329177349 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22475R_136 c22475R_72_2 (by norm_num)

theorem c22475R_72_0 : rowsJ2 72 73 0 300 ≤ 1808655302404083 :=
  rowsJ2_le_of_split 72 73 (by norm_num) (by norm_num) rows22475R_135 c22475R_72_1 (by norm_num)

theorem hr22475R_72 : rows2 72 73 ≤ 1808655302404083 := rows2_le_of_rowsJ2 72 73 c22475R_72_0

theorem c22475R_73_3 : rowsJ2 73 74 68 300 ≤ 35954985908148 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22475R_142 rows22475R_143 (by norm_num)

theorem c22475R_73_2 : rowsJ2 73 74 50 300 ≤ 405430769881177 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22475R_141 c22475R_73_3 (by norm_num)

theorem c22475R_73_1 : rowsJ2 73 74 35 300 ≤ 1170900144532977 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22475R_140 c22475R_73_2 (by norm_num)

theorem c22475R_73_0 : rowsJ2 73 74 0 300 ≤ 1740134347340559 :=
  rowsJ2_le_of_split 73 74 (by norm_num) (by norm_num) rows22475R_139 c22475R_73_1 (by norm_num)

theorem hr22475R_73 : rows2 73 74 ≤ 1740134347340559 := rows2_le_of_rowsJ2 73 74 c22475R_73_0

theorem c22475R_74_3 : rowsJ2 74 75 68 300 ≤ 35177777534092 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22475R_147 rows22475R_148 (by norm_num)

theorem c22475R_74_2 : rowsJ2 74 75 51 300 ≤ 340332073116583 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22475R_146 c22475R_74_3 (by norm_num)

theorem c22475R_74_1 : rowsJ2 74 75 35 300 ≤ 1121313993879593 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22475R_145 c22475R_74_2 (by norm_num)

theorem c22475R_74_0 : rowsJ2 74 75 0 300 ≤ 1674076741440871 :=
  rowsJ2_le_of_split 74 75 (by norm_num) (by norm_num) rows22475R_144 c22475R_74_1 (by norm_num)

theorem hr22475R_74 : rows2 74 75 ≤ 1674076741440871 := rows2_le_of_rowsJ2 74 75 c22475R_74_0

theorem c22475R_75_3 : rowsJ2 75 76 68 300 ≤ 33564331638427 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22475R_152 rows22475R_153 (by norm_num)

theorem c22475R_75_2 : rowsJ2 75 76 54 300 ≤ 226147752675315 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22475R_151 c22475R_75_3 (by norm_num)

theorem c22475R_75_1 : rowsJ2 75 76 35 300 ≤ 1066570581694264 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22475R_150 c22475R_75_2 (by norm_num)

theorem c22475R_75_0 : rowsJ2 75 76 0 300 ≤ 1606480193526034 :=
  rowsJ2_le_of_split 75 76 (by norm_num) (by norm_num) rows22475R_149 c22475R_75_1 (by norm_num)

theorem hr22475R_75 : rows2 75 76 ≤ 1606480193526034 := rows2_le_of_rowsJ2 75 76 c22475R_75_0

theorem c22475R_76_3 : rowsJ2 76 77 68 300 ≤ 31721668669512 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22475R_157 rows22475R_158 (by norm_num)

theorem c22475R_76_2 : rowsJ2 76 77 58 300 ≤ 122764958906653 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22475R_156 c22475R_76_3 (by norm_num)

theorem c22475R_76_1 : rowsJ2 76 77 35 300 ≤ 1012140285411954 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22475R_155 c22475R_76_2 (by norm_num)

theorem c22475R_76_0 : rowsJ2 76 77 0 300 ≤ 1542139664630654 :=
  rowsJ2_le_of_split 76 77 (by norm_num) (by norm_num) rows22475R_154 c22475R_76_1 (by norm_num)

theorem hr22475R_76 : rows2 76 77 ≤ 1542139664630654 := rows2_le_of_rowsJ2 76 77 c22475R_76_0

theorem c22475R_77_4 : rowsJ2 77 78 73 300 ≤ 14978570596763 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22475R_163 rows22475R_164 (by norm_num)

theorem c22475R_77_3 : rowsJ2 77 78 68 300 ≤ 29366569636051 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22475R_162 c22475R_77_4 (by norm_num)

theorem c22475R_77_2 : rowsJ2 77 78 59 300 ≤ 92485510428484 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22475R_161 c22475R_77_3 (by norm_num)

theorem c22475R_77_1 : rowsJ2 77 78 35 300 ≤ 953151545729390 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22475R_160 c22475R_77_2 (by norm_num)

theorem c22475R_77_0 : rowsJ2 77 78 0 300 ≤ 1476870699819087 :=
  rowsJ2_le_of_split 77 78 (by norm_num) (by norm_num) rows22475R_159 c22475R_77_1 (by norm_num)

theorem hr22475R_77 : rows2 77 78 ≤ 1476870699819087 := rows2_le_of_rowsJ2 77 78 c22475R_77_0

theorem c22475R_78_4 : rowsJ2 78 79 73 300 ≤ 14185435251282 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22475R_169 rows22475R_170 (by norm_num)

theorem c22475R_78_3 : rowsJ2 78 79 68 300 ≤ 26987582581395 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22475R_168 c22475R_78_4 (by norm_num)

theorem c22475R_78_2 : rowsJ2 78 79 60 300 ≤ 67648188371372 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22475R_167 c22475R_78_3 (by norm_num)

theorem c22475R_78_1 : rowsJ2 78 79 35 300 ≤ 895022378283689 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22475R_166 c22475R_78_2 (by norm_num)

theorem c22475R_78_0 : rowsJ2 78 79 0 300 ≤ 1415149421135211 :=
  rowsJ2_le_of_split 78 79 (by norm_num) (by norm_num) rows22475R_165 c22475R_78_1 (by norm_num)

theorem hr22475R_78 : rows2 78 79 ≤ 1415149421135211 := rows2_le_of_rowsJ2 78 79 c22475R_78_0

theorem c22475R_79_4 : rowsJ2 79 80 73 300 ≤ 12780249349253 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22475R_175 rows22475R_176 (by norm_num)

theorem c22475R_79_3 : rowsJ2 79 80 68 300 ≤ 24130565005570 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22475R_174 c22475R_79_4 (by norm_num)

theorem c22475R_79_2 : rowsJ2 79 80 61 300 ≤ 47681959602723 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22475R_173 c22475R_79_3 (by norm_num)

theorem c22475R_79_1 : rowsJ2 79 80 35 300 ≤ 837449763876328 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22475R_172 c22475R_79_2 (by norm_num)

theorem c22475R_79_0 : rowsJ2 79 80 0 300 ≤ 1352615441654152 :=
  rowsJ2_le_of_split 79 80 (by norm_num) (by norm_num) rows22475R_171 c22475R_79_1 (by norm_num)

theorem hr22475R_79 : rows2 79 80 ≤ 1352615441654152 := rows2_le_of_rowsJ2 79 80 c22475R_79_0

theorem c22475R_80_4 : rowsJ2 80 81 72 300 ≤ 13599078348562 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22475R_181 rows22475R_182 (by norm_num)

theorem c22475R_80_3 : rowsJ2 80 81 68 300 ≤ 21764978134395 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22475R_180 c22475R_80_4 (by norm_num)

theorem c22475R_80_2 : rowsJ2 80 81 61 300 ≤ 38739740217499 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22475R_179 c22475R_80_3 (by norm_num)

theorem c22475R_80_1 : rowsJ2 80 81 35 300 ≤ 781866768860082 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22475R_178 c22475R_80_2 (by norm_num)

theorem c22475R_80_0 : rowsJ2 80 81 0 300 ≤ 1294886368098153 :=
  rowsJ2_le_of_split 80 81 (by norm_num) (by norm_num) rows22475R_177 c22475R_80_1 (by norm_num)

theorem hr22475R_80 : rows2 80 81 ≤ 1294886368098153 := rows2_le_of_rowsJ2 80 81 c22475R_80_0

theorem c22475R_81_4 : rowsJ2 81 82 72 300 ≤ 12453281627160 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22475R_187 rows22475R_188 (by norm_num)

theorem c22475R_81_3 : rowsJ2 81 82 68 300 ≤ 19663778179721 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22475R_186 c22475R_81_4 (by norm_num)

theorem c22475R_81_2 : rowsJ2 81 82 61 300 ≤ 31286872268173 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22475R_185 c22475R_81_3 (by norm_num)

theorem c22475R_81_1 : rowsJ2 81 82 35 300 ≤ 728233249334836 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22475R_184 c22475R_81_2 (by norm_num)

theorem c22475R_81_0 : rowsJ2 81 82 0 300 ≤ 1237567605055686 :=
  rowsJ2_le_of_split 81 82 (by norm_num) (by norm_num) rows22475R_183 c22475R_81_1 (by norm_num)

theorem hr22475R_81 : rows2 81 82 ≤ 1237567605055686 := rows2_le_of_rowsJ2 81 82 c22475R_81_0

theorem c22475R_82_5 : rowsJ2 82 83 77 300 ≤ 7775999599232 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22475R_194 rows22475R_195 (by norm_num)

theorem c22475R_82_4 : rowsJ2 82 83 72 300 ≤ 12927058917575 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22475R_193 c22475R_82_5 (by norm_num)

theorem c22475R_82_3 : rowsJ2 82 83 68 300 ≤ 19283206101682 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22475R_192 c22475R_82_4 (by norm_num)

theorem c22475R_82_2 : rowsJ2 82 83 61 300 ≤ 26861532365523 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22475R_191 c22475R_82_3 (by norm_num)

theorem c22475R_82_1 : rowsJ2 82 83 35 300 ≤ 678179250870326 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22475R_190 c22475R_82_2 (by norm_num)

theorem c22475R_82_0 : rowsJ2 82 83 0 300 ≤ 1186156857971067 :=
  rowsJ2_le_of_split 82 83 (by norm_num) (by norm_num) rows22475R_189 c22475R_82_1 (by norm_num)

theorem hr22475R_82 : rows2 82 83 ≤ 1186156857971067 := rows2_le_of_rowsJ2 82 83 c22475R_82_0

theorem c22475R_83_4 : rowsJ2 83 84 73 300 ≤ 14425442743213 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22475R_200 rows22475R_201 (by norm_num)

theorem c22475R_83_3 : rowsJ2 83 84 68 300 ≤ 20643139385417 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22475R_199 c22475R_83_4 (by norm_num)

theorem c22475R_83_2 : rowsJ2 83 84 62 300 ≤ 23436355896993 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22475R_198 c22475R_83_3 (by norm_num)

theorem c22475R_83_1 : rowsJ2 83 84 36 300 ≤ 583656759115250 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22475R_197 c22475R_83_2 (by norm_num)

theorem c22475R_83_0 : rowsJ2 83 84 0 300 ≤ 1136782656544300 :=
  rowsJ2_le_of_split 83 84 (by norm_num) (by norm_num) rows22475R_196 c22475R_83_1 (by norm_num)

theorem hr22475R_83 : rows2 83 84 ≤ 1136782656544300 := rows2_le_of_rowsJ2 83 84 c22475R_83_0

theorem c22475R_84_5 : rowsJ2 84 85 78 300 ≤ 17879701790595 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22475R_207 rows22475R_208 (by norm_num)

theorem c22475R_84_4 : rowsJ2 84 85 73 300 ≤ 20176107227446 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22475R_206 c22475R_84_5 (by norm_num)

theorem c22475R_84_3 : rowsJ2 84 85 68 300 ≤ 25116795770498 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22475R_205 c22475R_84_4 (by norm_num)

theorem c22475R_84_2 : rowsJ2 84 85 62 300 ≤ 26974098260854 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22475R_204 c22475R_84_3 (by norm_num)

theorem c22475R_84_1 : rowsJ2 84 85 36 300 ≤ 544028097197497 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22475R_203 c22475R_84_2 (by norm_num)

theorem c22475R_84_0 : rowsJ2 84 85 0 300 ≤ 1094626436022828 :=
  rowsJ2_le_of_split 84 85 (by norm_num) (by norm_num) rows22475R_202 c22475R_84_1 (by norm_num)

theorem hr22475R_84 : rows2 84 85 ≤ 1094626436022828 := rows2_le_of_rowsJ2 84 85 c22475R_84_0

theorem c22475R_85_5 : rowsJ2 85 86 78 300 ≤ 27115890700413 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22475R_214 rows22475R_215 (by norm_num)

theorem c22475R_85_4 : rowsJ2 85 86 73 300 ≤ 28752629703356 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22475R_213 c22475R_85_5 (by norm_num)

theorem c22475R_85_3 : rowsJ2 85 86 68 300 ≤ 32296782755215 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22475R_212 c22475R_85_4 (by norm_num)

theorem c22475R_85_2 : rowsJ2 85 86 62 300 ≤ 33826899423169 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22475R_211 c22475R_85_3 (by norm_num)

theorem c22475R_85_1 : rowsJ2 85 86 37 300 ≤ 467349837548858 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22475R_210 c22475R_85_2 (by norm_num)

theorem c22475R_85_0 : rowsJ2 85 86 0 300 ≤ 1054985065774403 :=
  rowsJ2_le_of_split 85 86 (by norm_num) (by norm_num) rows22475R_209 c22475R_85_1 (by norm_num)

theorem hr22475R_85 : rows2 85 86 ≤ 1054985065774403 := rows2_le_of_rowsJ2 85 86 c22475R_85_0

theorem c22475R_86_5 : rowsJ2 86 87 77 300 ≤ 40190292618184 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22475R_221 rows22475R_222 (by norm_num)

theorem c22475R_86_4 : rowsJ2 86 87 72 300 ≤ 41294693795576 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22475R_220 c22475R_86_5 (by norm_num)

theorem c22475R_86_3 : rowsJ2 86 87 67 300 ≤ 44203938096865 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22475R_219 c22475R_86_4 (by norm_num)

theorem c22475R_86_2 : rowsJ2 86 87 62 300 ≤ 44910606963596 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22475R_218 c22475R_86_3 (by norm_num)

theorem c22475R_86_1 : rowsJ2 86 87 37 300 ≤ 440300377786652 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22475R_217 c22475R_86_2 (by norm_num)

theorem c22475R_86_0 : rowsJ2 86 87 0 300 ≤ 1023566589968785 :=
  rowsJ2_le_of_split 86 87 (by norm_num) (by norm_num) rows22475R_216 c22475R_86_1 (by norm_num)

theorem hr22475R_86 : rows2 86 87 ≤ 1023566589968785 := rows2_le_of_rowsJ2 86 87 c22475R_86_0

theorem c22475R_87_5 : rowsJ2 87 88 77 300 ≤ 55877656484778 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22475R_228 rows22475R_229 (by norm_num)

theorem c22475R_87_4 : rowsJ2 87 88 72 300 ≤ 56702338004415 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22475R_227 c22475R_87_5 (by norm_num)

theorem c22475R_87_3 : rowsJ2 87 88 67 300 ≤ 58578577497405 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22475R_226 c22475R_87_4 (by norm_num)

theorem c22475R_87_2 : rowsJ2 87 88 62 300 ≤ 59278095461059 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22475R_225 c22475R_87_3 (by norm_num)

theorem c22475R_87_1 : rowsJ2 87 88 38 300 ≤ 382868992954360 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22475R_224 c22475R_87_2 (by norm_num)

theorem c22475R_87_0 : rowsJ2 87 88 0 300 ≤ 995118123821034 :=
  rowsJ2_le_of_split 87 88 (by norm_num) (by norm_num) rows22475R_223 c22475R_87_1 (by norm_num)

theorem hr22475R_87 : rows2 87 88 ≤ 995118123821034 := rows2_le_of_rowsJ2 87 88 c22475R_87_0

theorem c22475R_88_5 : rowsJ2 88 89 78 300 ≤ 246435057043548 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22475R_235 rows22475R_236 (by norm_num)

theorem c22475R_88_4 : rowsJ2 88 89 72 300 ≤ 248488744372882 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22475R_234 c22475R_88_5 (by norm_num)

theorem c22475R_88_3 : rowsJ2 88 89 67 300 ≤ 249563311277400 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22475R_233 c22475R_88_4 (by norm_num)

theorem c22475R_88_2 : rowsJ2 88 89 62 300 ≤ 250255856797534 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22475R_232 c22475R_88_3 (by norm_num)

theorem c22475R_88_1 : rowsJ2 88 89 39 300 ≤ 509977744439068 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22475R_231 c22475R_88_2 (by norm_num)

theorem c22475R_88_0 : rowsJ2 88 89 0 300 ≤ 1147118847222626 :=
  rowsJ2_le_of_split 88 89 (by norm_num) (by norm_num) rows22475R_230 c22475R_88_1 (by norm_num)

theorem hr22475R_88 : rows2 88 89 ≤ 1147118847222626 := rows2_le_of_rowsJ2 88 89 c22475R_88_0

theorem c22475R_89_5 : rowsJ2 89 90 78 300 ≤ 387455232246034 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22475R_242 rows22475R_243 (by norm_num)

theorem c22475R_89_4 : rowsJ2 89 90 72 300 ≤ 390086106144916 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22475R_241 c22475R_89_5 (by norm_num)

theorem c22475R_89_3 : rowsJ2 89 90 67 300 ≤ 390588115375252 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22475R_240 c22475R_89_4 (by norm_num)

theorem c22475R_89_2 : rowsJ2 89 90 62 300 ≤ 391100111045477 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22475R_239 c22475R_89_3 (by norm_num)

theorem c22475R_89_1 : rowsJ2 89 90 40 300 ≤ 594704465178841 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22475R_238 c22475R_89_2 (by norm_num)

theorem c22475R_89_0 : rowsJ2 89 90 0 300 ≤ 1248843556835059 :=
  rowsJ2_le_of_split 89 90 (by norm_num) (by norm_num) rows22475R_237 c22475R_89_1 (by norm_num)

theorem hr22475R_89 : rows2 89 90 ≤ 1248843556835059 := rows2_le_of_rowsJ2 89 90 c22475R_89_0

theorem c22475R_90_5 : rowsJ2 90 91 78 300 ≤ 648219275783123 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22475R_249 rows22475R_250 (by norm_num)

theorem c22475R_90_4 : rowsJ2 90 91 72 300 ≤ 651787050868966 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22475R_248 c22475R_90_5 (by norm_num)

theorem c22475R_90_3 : rowsJ2 90 91 67 300 ≤ 651945908108790 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22475R_247 c22475R_90_4 (by norm_num)

theorem c22475R_90_2 : rowsJ2 90 91 62 300 ≤ 652323236180446 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22475R_246 c22475R_90_3 (by norm_num)

theorem c22475R_90_1 : rowsJ2 90 91 43 300 ≤ 765718175631254 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22475R_245 c22475R_90_2 (by norm_num)

theorem c22475R_90_0 : rowsJ2 90 91 0 300 ≤ 1474708811593779 :=
  rowsJ2_le_of_split 90 91 (by norm_num) (by norm_num) rows22475R_244 c22475R_90_1 (by norm_num)

theorem hr22475R_90 : rows2 90 91 ≤ 1474708811593779 := rows2_le_of_rowsJ2 90 91 c22475R_90_0

theorem c22475R_91_5 : rowsJ2 91 92 78 300 ≤ 774792333267499 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22475R_256 rows22475R_257 (by norm_num)

theorem c22475R_91_4 : rowsJ2 91 92 72 300 ≤ 779198545859930 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22475R_255 c22475R_91_5 (by norm_num)

theorem c22475R_91_3 : rowsJ2 91 92 67 300 ≤ 779221124756143 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22475R_254 c22475R_91_4 (by norm_num)

theorem c22475R_91_2 : rowsJ2 91 92 62 300 ≤ 779399019560557 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22475R_253 c22475R_91_3 (by norm_num)

theorem c22475R_91_1 : rowsJ2 91 92 48 300 ≤ 810168008274885 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22475R_252 c22475R_91_2 (by norm_num)

theorem c22475R_91_0 : rowsJ2 91 92 0 300 ≤ 1565746900677568 :=
  rowsJ2_le_of_split 91 92 (by norm_num) (by norm_num) rows22475R_251 c22475R_91_1 (by norm_num)

theorem hr22475R_91 : rows2 91 92 ≤ 1565746900677568 := rows2_le_of_rowsJ2 91 92 c22475R_91_0

theorem c22475R_92_5 : rowsJ2 92 93 78 300 ≤ 1018669278279397 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22475R_263 rows22475R_264 (by norm_num)

theorem c22475R_92_4 : rowsJ2 92 93 72 300 ≤ 1024215276667123 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22475R_262 c22475R_92_5 (by norm_num)

theorem c22475R_92_3 : rowsJ2 92 93 67 300 ≤ 1024215276667123 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22475R_261 c22475R_92_4 (by norm_num)

theorem c22475R_92_2 : rowsJ2 92 93 62 300 ≤ 1024281471152102 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22475R_260 c22475R_92_3 (by norm_num)

theorem c22475R_92_1 : rowsJ2 92 93 51 300 ≤ 1030421908194308 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22475R_259 c22475R_92_2 (by norm_num)

theorem c22475R_92_0 : rowsJ2 92 93 0 300 ≤ 1778581592340411 :=
  rowsJ2_le_of_split 92 93 (by norm_num) (by norm_num) rows22475R_258 c22475R_92_1 (by norm_num)

theorem hr22475R_92 : rows2 92 93 ≤ 1778581592340411 := rows2_le_of_rowsJ2 92 93 c22475R_92_0

theorem c22475R_93_5 : rowsJ2 93 94 77 300 ≤ 1133845944982513 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22475R_270 rows22475R_271 (by norm_num)

theorem c22475R_93_4 : rowsJ2 93 94 71 300 ≤ 1137954178865207 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22475R_269 c22475R_93_5 (by norm_num)

theorem c22475R_93_3 : rowsJ2 93 94 66 300 ≤ 1137954178865207 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22475R_268 c22475R_93_4 (by norm_num)

theorem c22475R_93_2 : rowsJ2 93 94 61 300 ≤ 1137954178865207 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22475R_267 c22475R_93_3 (by norm_num)

theorem c22475R_93_1 : rowsJ2 93 94 52 300 ≤ 1139217846451832 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22475R_266 c22475R_93_2 (by norm_num)

theorem c22475R_93_0 : rowsJ2 93 94 0 300 ≤ 1859399893099657 :=
  rowsJ2_le_of_split 93 94 (by norm_num) (by norm_num) rows22475R_265 c22475R_93_1 (by norm_num)

theorem hr22475R_93 : rows2 93 94 ≤ 1859399893099657 := rows2_le_of_rowsJ2 93 94 c22475R_93_0

theorem c22475R_94_4 : rowsJ2 94 95 72 300 ≤ 1366913992668203 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22475R_276 rows22475R_277 (by norm_num)

theorem c22475R_94_3 : rowsJ2 94 95 66 300 ≤ 1366985352642999 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22475R_275 c22475R_94_4 (by norm_num)

theorem c22475R_94_2 : rowsJ2 94 95 61 300 ≤ 1366985352642999 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22475R_274 c22475R_94_3 (by norm_num)

theorem c22475R_94_1 : rowsJ2 94 95 53 300 ≤ 1366985352642999 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22475R_273 c22475R_94_2 (by norm_num)

theorem c22475R_94_0 : rowsJ2 94 95 0 300 ≤ 2059087833831656 :=
  rowsJ2_le_of_split 94 95 (by norm_num) (by norm_num) rows22475R_272 c22475R_94_1 (by norm_num)

theorem hr22475R_94 : rows2 94 95 ≤ 2059087833831656 := rows2_le_of_rowsJ2 94 95 c22475R_94_0

theorem c22475R_95_4 : rowsJ2 95 96 72 300 ≤ 1467584936042102 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22475R_282 rows22475R_283 (by norm_num)

theorem c22475R_95_3 : rowsJ2 95 96 66 300 ≤ 1467657782849723 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22475R_281 c22475R_95_4 (by norm_num)

theorem c22475R_95_2 : rowsJ2 95 96 61 300 ≤ 1467657782849723 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22475R_280 c22475R_95_3 (by norm_num)

theorem c22475R_95_1 : rowsJ2 95 96 53 300 ≤ 1467657782849723 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22475R_279 c22475R_95_2 (by norm_num)

theorem c22475R_95_0 : rowsJ2 95 96 0 300 ≤ 2129994205801733 :=
  rowsJ2_le_of_split 95 96 (by norm_num) (by norm_num) rows22475R_278 c22475R_95_1 (by norm_num)

theorem hr22475R_95 : rows2 95 96 ≤ 2129994205801733 := rows2_le_of_rowsJ2 95 96 c22475R_95_0

theorem c22475R_96_4 : rowsJ2 96 97 72 300 ≤ 1681194602161824 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22475R_288 rows22475R_289 (by norm_num)

theorem c22475R_96_3 : rowsJ2 96 97 66 300 ≤ 1681342344703108 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22475R_287 c22475R_96_4 (by norm_num)

theorem c22475R_96_2 : rowsJ2 96 97 61 300 ≤ 1681342344703108 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22475R_286 c22475R_96_3 (by norm_num)

theorem c22475R_96_1 : rowsJ2 96 97 53 300 ≤ 1681342344703108 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22475R_285 c22475R_96_2 (by norm_num)

theorem c22475R_96_0 : rowsJ2 96 97 0 300 ≤ 2317466995218397 :=
  rowsJ2_le_of_split 96 97 (by norm_num) (by norm_num) rows22475R_284 c22475R_96_1 (by norm_num)

theorem hr22475R_96 : rows2 96 97 ≤ 2317466995218397 := rows2_le_of_rowsJ2 96 97 c22475R_96_0

theorem c22475R_97_4 : rowsJ2 97 98 72 300 ≤ 1616349299786003 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22475R_294 rows22475R_295 (by norm_num)

theorem c22475R_97_3 : rowsJ2 97 98 66 300 ≤ 1616500224691220 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22475R_293 c22475R_97_4 (by norm_num)

theorem c22475R_97_2 : rowsJ2 97 98 61 300 ≤ 1616500224691220 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22475R_292 c22475R_97_3 (by norm_num)

theorem c22475R_97_1 : rowsJ2 97 98 53 300 ≤ 1616500224691220 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22475R_291 c22475R_97_2 (by norm_num)

theorem c22475R_97_0 : rowsJ2 97 98 0 300 ≤ 2225628602581031 :=
  rowsJ2_le_of_split 97 98 (by norm_num) (by norm_num) rows22475R_290 c22475R_97_1 (by norm_num)

theorem hr22475R_97 : rows2 97 98 ≤ 2225628602581031 := rows2_le_of_rowsJ2 97 98 c22475R_97_0

theorem c22475R_98_4 : rowsJ2 98 99 72 300 ≤ 1599698434962009 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22475R_300 rows22475R_301 (by norm_num)

theorem c22475R_98_3 : rowsJ2 98 99 66 300 ≤ 1599928125514255 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22475R_299 c22475R_98_4 (by norm_num)

theorem c22475R_98_2 : rowsJ2 98 99 61 300 ≤ 1599928125514255 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22475R_298 c22475R_98_3 (by norm_num)

theorem c22475R_98_1 : rowsJ2 98 99 53 300 ≤ 1600211565587964 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22475R_297 c22475R_98_2 (by norm_num)

theorem c22475R_98_0 : rowsJ2 98 99 0 300 ≤ 2185874519594569 :=
  rowsJ2_le_of_split 98 99 (by norm_num) (by norm_num) rows22475R_296 c22475R_98_1 (by norm_num)

theorem hr22475R_98 : rows2 98 99 ≤ 2185874519594569 := rows2_le_of_rowsJ2 98 99 c22475R_98_0

theorem c22475R_99_4 : rowsJ2 99 100 71 300 ≤ 1468151646565447 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22475R_306 rows22475R_307 (by norm_num)

theorem c22475R_99_3 : rowsJ2 99 100 65 300 ≤ 1468151646565447 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22475R_305 c22475R_99_4 (by norm_num)

theorem c22475R_99_2 : rowsJ2 99 100 60 300 ≤ 1468151646565447 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22475R_304 c22475R_99_3 (by norm_num)

theorem c22475R_99_1 : rowsJ2 99 100 53 300 ≤ 1469126975882722 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22475R_303 c22475R_99_2 (by norm_num)

theorem c22475R_99_0 : rowsJ2 99 100 0 300 ≤ 2030362646326283 :=
  rowsJ2_le_of_split 99 100 (by norm_num) (by norm_num) rows22475R_302 c22475R_99_1 (by norm_num)

theorem hr22475R_99 : rows2 99 100 ≤ 2030362646326283 := rows2_le_of_rowsJ2 99 100 c22475R_99_0

theorem c22475R_100_4 : rowsJ2 100 101 73 300 ≤ 1451535152427626 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22475R_312 rows22475R_313 (by norm_num)

theorem c22475R_100_3 : rowsJ2 100 101 66 300 ≤ 1452574664364219 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22475R_311 c22475R_100_4 (by norm_num)

theorem c22475R_100_2 : rowsJ2 100 101 60 300 ≤ 1452574664364219 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22475R_310 c22475R_100_3 (by norm_num)

theorem c22475R_100_1 : rowsJ2 100 101 53 300 ≤ 1454660910652953 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22475R_309 c22475R_100_2 (by norm_num)

theorem c22475R_100_0 : rowsJ2 100 101 0 300 ≤ 1994287558669900 :=
  rowsJ2_le_of_split 100 101 (by norm_num) (by norm_num) rows22475R_308 c22475R_100_1 (by norm_num)

theorem hr22475R_100 : rows2 100 101 ≤ 1994287558669900 := rows2_le_of_rowsJ2 100 101 c22475R_100_0

theorem c22475R_101_4 : rowsJ2 101 102 73 300 ≤ 1322904289380808 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22475R_318 rows22475R_319 (by norm_num)

theorem c22475R_101_3 : rowsJ2 101 102 66 300 ≤ 1324047861302736 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22475R_317 c22475R_101_4 (by norm_num)

theorem c22475R_101_2 : rowsJ2 101 102 60 300 ≤ 1324047861302736 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22475R_316 c22475R_101_3 (by norm_num)

theorem c22475R_101_1 : rowsJ2 101 102 53 300 ≤ 1327873530625190 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22475R_315 c22475R_101_2 (by norm_num)

theorem c22475R_101_0 : rowsJ2 101 102 0 300 ≤ 1845174821493039 :=
  rowsJ2_le_of_split 101 102 (by norm_num) (by norm_num) rows22475R_314 c22475R_101_1 (by norm_num)

theorem hr22475R_101 : rows2 101 102 ≤ 1845174821493039 := rows2_le_of_rowsJ2 101 102 c22475R_101_0

theorem c22475R_102_3 : rowsJ2 102 103 66 300 ≤ 1309454188372376 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22475R_323 rows22475R_324 (by norm_num)

theorem c22475R_102_2 : rowsJ2 102 103 60 300 ≤ 1309454188372376 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22475R_322 c22475R_102_3 (by norm_num)

theorem c22475R_102_1 : rowsJ2 102 103 53 300 ≤ 1315585089358659 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22475R_321 c22475R_102_2 (by norm_num)

theorem c22475R_102_0 : rowsJ2 102 103 0 300 ≤ 1813279806822149 :=
  rowsJ2_le_of_split 102 103 (by norm_num) (by norm_num) rows22475R_320 c22475R_102_1 (by norm_num)

theorem hr22475R_102 : rows2 102 103 ≤ 1813279806822149 := rows2_le_of_rowsJ2 102 103 c22475R_102_0

theorem c22475R_103_3 : rowsJ2 103 104 66 300 ≤ 1184103511344566 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22475R_328 rows22475R_329 (by norm_num)

theorem c22475R_103_2 : rowsJ2 103 104 60 300 ≤ 1184103511344566 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22475R_327 c22475R_103_3 (by norm_num)

theorem c22475R_103_1 : rowsJ2 103 104 53 300 ≤ 1193402284472812 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22475R_326 c22475R_103_2 (by norm_num)

theorem c22475R_103_0 : rowsJ2 103 104 0 300 ≤ 1670125609450893 :=
  rowsJ2_le_of_split 103 104 (by norm_num) (by norm_num) rows22475R_325 c22475R_103_1 (by norm_num)

theorem hr22475R_103 : rows2 103 104 ≤ 1670125609450893 := rows2_le_of_rowsJ2 103 104 c22475R_103_0

theorem c22475R_104_3 : rowsJ2 104 105 66 300 ≤ 1170493433431679 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22475R_333 rows22475R_334 (by norm_num)

theorem c22475R_104_2 : rowsJ2 104 105 60 300 ≤ 1170493433431679 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22475R_332 c22475R_104_3 (by norm_num)

theorem c22475R_104_1 : rowsJ2 104 105 53 300 ≤ 1183590806722085 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22475R_331 c22475R_104_2 (by norm_num)

theorem c22475R_104_0 : rowsJ2 104 105 0 300 ≤ 1642186346622150 :=
  rowsJ2_le_of_split 104 105 (by norm_num) (by norm_num) rows22475R_330 c22475R_104_1 (by norm_num)

theorem hr22475R_104 : rows2 104 105 ≤ 1642186346622150 := rows2_le_of_rowsJ2 104 105 c22475R_104_0

theorem c22475R_105_3 : rowsJ2 105 106 65 300 ≤ 1048160870358120 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22475R_338 rows22475R_339 (by norm_num)

theorem c22475R_105_2 : rowsJ2 105 106 59 300 ≤ 1049850755316475 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22475R_337 c22475R_105_3 (by norm_num)

theorem c22475R_105_1 : rowsJ2 105 106 53 300 ≤ 1065692288563162 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22475R_336 c22475R_105_2 (by norm_num)

theorem c22475R_105_0 : rowsJ2 105 106 0 300 ≤ 1504805247653205 :=
  rowsJ2_le_of_split 105 106 (by norm_num) (by norm_num) rows22475R_335 c22475R_105_1 (by norm_num)

theorem hr22475R_105 : rows2 105 106 ≤ 1504805247653205 := rows2_le_of_rowsJ2 105 106 c22475R_105_0

theorem c22475R_106_3 : rowsJ2 106 107 65 300 ≤ 1035547683219675 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22475R_343 rows22475R_344 (by norm_num)

theorem c22475R_106_2 : rowsJ2 106 107 59 300 ≤ 1038618564033757 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22475R_342 c22475R_106_3 (by norm_num)

theorem c22475R_106_1 : rowsJ2 106 107 52 300 ≤ 1061083642388892 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22475R_341 c22475R_106_2 (by norm_num)

theorem c22475R_106_0 : rowsJ2 106 107 0 300 ≤ 1480113125390401 :=
  rowsJ2_le_of_split 106 107 (by norm_num) (by norm_num) rows22475R_340 c22475R_106_1 (by norm_num)

theorem hr22475R_106 : rows2 106 107 ≤ 1480113125390401 := rows2_le_of_rowsJ2 106 107 c22475R_106_0

theorem c22475R_107_3 : rowsJ2 107 108 66 300 ≤ 916177668964847 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22475R_348 rows22475R_349 (by norm_num)

theorem c22475R_107_2 : rowsJ2 107 108 59 300 ≤ 920905436940237 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22475R_347 c22475R_107_3 (by norm_num)

theorem c22475R_107_1 : rowsJ2 107 108 52 300 ≤ 947052043375255 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22475R_346 c22475R_107_2 (by norm_num)

theorem c22475R_107_0 : rowsJ2 107 108 0 300 ≤ 1347756057368695 :=
  rowsJ2_le_of_split 107 108 (by norm_num) (by norm_num) rows22475R_345 c22475R_107_1 (by norm_num)

theorem hr22475R_107 : rows2 107 108 ≤ 1347756057368695 := rows2_le_of_rowsJ2 107 108 c22475R_107_0

theorem c22475R_108_3 : rowsJ2 108 109 66 300 ≤ 906485593232142 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22475R_353 rows22475R_354 (by norm_num)

theorem c22475R_108_2 : rowsJ2 108 109 59 300 ≤ 912862313452756 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22475R_352 c22475R_108_3 (by norm_num)

theorem c22475R_108_1 : rowsJ2 108 109 52 300 ≤ 942556673329657 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22475R_351 c22475R_108_2 (by norm_num)

theorem c22475R_108_0 : rowsJ2 108 109 0 300 ≤ 1327553459025615 :=
  rowsJ2_le_of_split 108 109 (by norm_num) (by norm_num) rows22475R_350 c22475R_108_1 (by norm_num)

theorem hr22475R_108 : rows2 108 109 ≤ 1327553459025615 := rows2_le_of_rowsJ2 108 109 c22475R_108_0

theorem c22475R_109_3 : rowsJ2 109 110 65 300 ≤ 791823072973340 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22475R_358 rows22475R_359 (by norm_num)

theorem c22475R_109_2 : rowsJ2 109 110 58 300 ≤ 803253582943750 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22475R_357 c22475R_109_3 (by norm_num)

theorem c22475R_109_1 : rowsJ2 109 110 52 300 ≤ 832901587630948 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22475R_356 c22475R_109_2 (by norm_num)

theorem c22475R_109_0 : rowsJ2 109 110 0 300 ≤ 1201064987918770 :=
  rowsJ2_le_of_split 109 110 (by norm_num) (by norm_num) rows22475R_355 c22475R_109_1 (by norm_num)

theorem hr22475R_109 : rows2 109 110 ≤ 1201064987918770 := rows2_le_of_rowsJ2 109 110 c22475R_109_0

theorem c22475R_110_3 : rowsJ2 110 111 65 300 ≤ 786229893664546 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22475R_363 rows22475R_364 (by norm_num)

theorem c22475R_110_2 : rowsJ2 110 111 58 300 ≤ 799090631240657 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22475R_362 c22475R_110_3 (by norm_num)

theorem c22475R_110_1 : rowsJ2 110 111 52 300 ≤ 831603995148467 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22475R_361 c22475R_110_2 (by norm_num)

theorem c22475R_110_0 : rowsJ2 110 111 0 300 ≤ 1185690797256568 :=
  rowsJ2_le_of_split 110 111 (by norm_num) (by norm_num) rows22475R_360 c22475R_110_1 (by norm_num)

theorem hr22475R_110 : rows2 110 111 ≤ 1185690797256568 := rows2_le_of_rowsJ2 110 111 c22475R_110_0

theorem c22475R_111_3 : rowsJ2 111 112 65 300 ≤ 675590524029220 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22475R_368 rows22475R_369 (by norm_num)

theorem c22475R_111_2 : rowsJ2 111 112 58 300 ≤ 689594541429941 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22475R_367 c22475R_111_3 (by norm_num)

theorem c22475R_111_1 : rowsJ2 111 112 51 300 ≤ 730051812683088 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22475R_366 c22475R_111_2 (by norm_num)

theorem c22475R_111_0 : rowsJ2 111 112 0 300 ≤ 1063446821332903 :=
  rowsJ2_le_of_split 111 112 (by norm_num) (by norm_num) rows22475R_365 c22475R_111_1 (by norm_num)

theorem hr22475R_111 : rows2 111 112 ≤ 1063446821332903 := rows2_le_of_rowsJ2 111 112 c22475R_111_0

theorem c22475R_112_2 : rowsJ2 112 113 58 300 ≤ 686691697341561 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22475R_372 rows22475R_373 (by norm_num)

theorem c22475R_112_1 : rowsJ2 112 113 51 300 ≤ 729919352106033 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22475R_371 c22475R_112_2 (by norm_num)

theorem c22475R_112_0 : rowsJ2 112 113 0 300 ≤ 1050214204746922 :=
  rowsJ2_le_of_split 112 113 (by norm_num) (by norm_num) rows22475R_370 c22475R_112_1 (by norm_num)

theorem hr22475R_112 : rows2 112 113 ≤ 1050214204746922 := rows2_le_of_rowsJ2 112 113 c22475R_112_0

theorem c22475R_113_2 : rowsJ2 113 114 58 300 ≤ 576980923486210 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22475R_376 rows22475R_377 (by norm_num)

theorem c22475R_113_1 : rowsJ2 113 114 51 300 ≤ 622379436940146 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22475R_375 c22475R_113_2 (by norm_num)

theorem c22475R_113_0 : rowsJ2 113 114 0 300 ≤ 928715020079845 :=
  rowsJ2_le_of_split 113 114 (by norm_num) (by norm_num) rows22475R_374 c22475R_113_1 (by norm_num)

theorem hr22475R_113 : rows2 113 114 ≤ 928715020079845 := rows2_le_of_rowsJ2 113 114 c22475R_113_0

theorem c22475R_114_2 : rowsJ2 114 115 58 300 ≤ 573135521265776 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22475R_380 rows22475R_381 (by norm_num)

theorem c22475R_114_1 : rowsJ2 114 115 51 300 ≤ 620406384278299 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22475R_379 c22475R_114_2 (by norm_num)

theorem c22475R_114_0 : rowsJ2 114 115 0 300 ≤ 915289317385828 :=
  rowsJ2_le_of_split 114 115 (by norm_num) (by norm_num) rows22475R_378 c22475R_114_1 (by norm_num)

theorem hr22475R_114 : rows2 114 115 ≤ 915289317385828 := rows2_le_of_rowsJ2 114 115 c22475R_114_0

theorem c22475R_115_2 : rowsJ2 115 116 57 300 ≤ 466550115088262 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22475R_384 rows22475R_385 (by norm_num)

theorem c22475R_115_1 : rowsJ2 115 116 50 300 ≤ 517650880447103 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22475R_383 c22475R_115_2 (by norm_num)

theorem c22475R_115_0 : rowsJ2 115 116 0 300 ≤ 792996423098322 :=
  rowsJ2_le_of_split 115 116 (by norm_num) (by norm_num) rows22475R_382 c22475R_115_1 (by norm_num)

theorem hr22475R_115 : rows2 115 116 ≤ 792996423098322 := rows2_le_of_rowsJ2 115 116 c22475R_115_0

theorem c22475R_116_2 : rowsJ2 116 117 57 300 ≤ 462034482862203 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22475R_388 rows22475R_389 (by norm_num)

theorem c22475R_116_1 : rowsJ2 116 117 50 300 ≤ 514600950905854 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22475R_387 c22475R_116_2 (by norm_num)

theorem c22475R_116_0 : rowsJ2 116 117 0 300 ≤ 779686435061700 :=
  rowsJ2_le_of_split 116 117 (by norm_num) (by norm_num) rows22475R_386 c22475R_116_1 (by norm_num)

theorem hr22475R_116 : rows2 116 117 ≤ 779686435061700 := rows2_le_of_rowsJ2 116 117 c22475R_116_0

theorem c22475R_117_2 : rowsJ2 117 118 57 300 ≤ 350801178590585 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22475R_392 rows22475R_393 (by norm_num)

theorem c22475R_117_1 : rowsJ2 117 118 50 300 ≤ 403889079910816 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22475R_391 c22475R_117_2 (by norm_num)

theorem c22475R_117_0 : rowsJ2 117 118 0 300 ≤ 657874315143064 :=
  rowsJ2_le_of_split 117 118 (by norm_num) (by norm_num) rows22475R_390 c22475R_117_1 (by norm_num)

theorem hr22475R_117 : rows2 117 118 ≤ 657874315143064 := rows2_le_of_rowsJ2 117 118 c22475R_117_0

theorem c22475R_118_2 : rowsJ2 118 119 56 300 ≤ 352063346929971 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22475R_396 rows22475R_397 (by norm_num)

theorem c22475R_118_1 : rowsJ2 118 119 49 300 ≤ 408905316329135 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22475R_395 c22475R_118_2 (by norm_num)

theorem c22475R_118_0 : rowsJ2 118 119 0 300 ≤ 645961421225076 :=
  rowsJ2_le_of_split 118 119 (by norm_num) (by norm_num) rows22475R_394 c22475R_118_1 (by norm_num)

theorem hr22475R_118 : rows2 118 119 ≤ 645961421225076 := rows2_le_of_rowsJ2 118 119 c22475R_118_0

theorem c22475R_119_2 : rowsJ2 119 120 56 300 ≤ 341792937628252 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22475R_400 rows22475R_401 (by norm_num)

theorem c22475R_119_1 : rowsJ2 119 120 49 300 ≤ 398635761099153 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22475R_399 c22475R_119_2 (by norm_num)

theorem c22475R_119_0 : rowsJ2 119 120 0 300 ≤ 625883886392555 :=
  rowsJ2_le_of_split 119 120 (by norm_num) (by norm_num) rows22475R_398 c22475R_119_1 (by norm_num)

theorem hr22475R_119 : rows2 119 120 ≤ 625883886392555 := rows2_le_of_rowsJ2 119 120 c22475R_119_0

theorem c22475R_120_2 : rowsJ2 120 121 56 300 ≤ 538568341572669 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22475R_404 rows22475R_405 (by norm_num)

theorem c22475R_120_1 : rowsJ2 120 121 49 300 ≤ 595028819279168 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22475R_403 c22475R_120_2 (by norm_num)

theorem c22475R_120_0 : rowsJ2 120 121 0 300 ≤ 814832234427485 :=
  rowsJ2_le_of_split 120 121 (by norm_num) (by norm_num) rows22475R_402 c22475R_120_1 (by norm_num)

theorem hr22475R_120 : rows2 120 121 ≤ 814832234427485 := rows2_le_of_rowsJ2 120 121 c22475R_120_0

theorem c22475R_121_2 : rowsJ2 121 122 57 300 ≤ 614368992463288 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22475R_408 rows22475R_409 (by norm_num)

theorem c22475R_121_1 : rowsJ2 121 122 49 300 ≤ 672876169635990 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22475R_407 c22475R_121_2 (by norm_num)

theorem c22475R_121_0 : rowsJ2 121 122 0 300 ≤ 884732539726999 :=
  rowsJ2_le_of_split 121 122 (by norm_num) (by norm_num) rows22475R_406 c22475R_121_1 (by norm_num)

theorem hr22475R_121 : rows2 121 122 ≤ 884732539726999 := rows2_le_of_rowsJ2 121 122 c22475R_121_0

theorem c22475R_122_2 : rowsJ2 122 123 56 300 ≤ 806166231577237 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22475R_412 rows22475R_413 (by norm_num)

theorem c22475R_122_1 : rowsJ2 122 123 48 300 ≤ 869214013196126 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22475R_411 c22475R_122_2 (by norm_num)

theorem c22475R_122_0 : rowsJ2 122 123 0 300 ≤ 1065460875617094 :=
  rowsJ2_le_of_split 122 123 (by norm_num) (by norm_num) rows22475R_410 c22475R_122_1 (by norm_num)

theorem hr22475R_122 : rows2 122 123 ≤ 1065460875617094 := rows2_le_of_rowsJ2 122 123 c22475R_122_0

theorem c22475R_123_2 : rowsJ2 123 124 56 300 ≤ 872948630470585 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22475R_416 rows22475R_417 (by norm_num)

theorem c22475R_123_1 : rowsJ2 123 124 48 300 ≤ 933645550358484 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22475R_415 c22475R_123_2 (by norm_num)

theorem c22475R_123_0 : rowsJ2 123 124 0 300 ≤ 1123198438407612 :=
  rowsJ2_le_of_split 123 124 (by norm_num) (by norm_num) rows22475R_414 c22475R_123_1 (by norm_num)

theorem hr22475R_123 : rows2 123 124 ≤ 1123198438407612 := rows2_le_of_rowsJ2 123 124 c22475R_123_0

theorem c22475R_124_2 : rowsJ2 124 125 56 300 ≤ 1052570399345418 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22475R_420 rows22475R_421 (by norm_num)

theorem c22475R_124_1 : rowsJ2 124 125 48 300 ≤ 1110785909727513 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22475R_419 c22475R_124_2 (by norm_num)

theorem c22475R_124_0 : rowsJ2 124 125 0 300 ≤ 1296005195275263 :=
  rowsJ2_le_of_split 124 125 (by norm_num) (by norm_num) rows22475R_418 c22475R_124_1 (by norm_num)

theorem hr22475R_124 : rows2 124 125 ≤ 1296005195275263 := rows2_le_of_rowsJ2 124 125 c22475R_124_0

theorem c22475R_125_2 : rowsJ2 125 126 55 300 ≤ 1231916153531900 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22475R_424 rows22475R_425 (by norm_num)

theorem c22475R_125_1 : rowsJ2 125 126 47 300 ≤ 1294789193663514 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22475R_423 c22475R_125_2 (by norm_num)

theorem c22475R_125_0 : rowsJ2 125 126 0 300 ≤ 1464144793006057 :=
  rowsJ2_le_of_split 125 126 (by norm_num) (by norm_num) rows22475R_422 c22475R_125_1 (by norm_num)

theorem hr22475R_125 : rows2 125 126 ≤ 1464144793006057 := rows2_le_of_rowsJ2 125 126 c22475R_125_0

theorem c22475R_126_1 : rowsJ2 126 127 47 300 ≤ 1464415758553359 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22475R_427 rows22475R_428 (by norm_num)

theorem c22475R_126_0 : rowsJ2 126 127 0 300 ≤ 1630643035969948 :=
  rowsJ2_le_of_split 126 127 (by norm_num) (by norm_num) rows22475R_426 c22475R_126_1 (by norm_num)

theorem hr22475R_126 : rows2 126 127 ≤ 1630643035969948 := rows2_le_of_rowsJ2 126 127 c22475R_126_0

theorem c22475R_127_1 : rowsJ2 127 128 47 300 ≤ 1620526926371109 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22475R_430 rows22475R_431 (by norm_num)

theorem c22475R_127_0 : rowsJ2 127 128 0 300 ≤ 1783530080149461 :=
  rowsJ2_le_of_split 127 128 (by norm_num) (by norm_num) rows22475R_429 c22475R_127_1 (by norm_num)

theorem hr22475R_127 : rows2 127 128 ≤ 1783530080149461 := rows2_le_of_rowsJ2 127 128 c22475R_127_0

theorem c22475R_128_1 : rowsJ2 128 129 46 300 ≤ 1787016460033837 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22475R_433 rows22475R_434 (by norm_num)

theorem c22475R_128_0 : rowsJ2 128 129 0 300 ≤ 1936384223233014 :=
  rowsJ2_le_of_split 128 129 (by norm_num) (by norm_num) rows22475R_432 c22475R_128_1 (by norm_num)

theorem hr22475R_128 : rows2 128 129 ≤ 1936384223233014 := rows2_le_of_rowsJ2 128 129 c22475R_128_0

theorem c22475R_129_1 : rowsJ2 129 130 46 300 ≤ 1929312302979349 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22475R_436 rows22475R_437 (by norm_num)

theorem c22475R_129_0 : rowsJ2 129 130 0 300 ≤ 2076806959546209 :=
  rowsJ2_le_of_split 129 130 (by norm_num) (by norm_num) rows22475R_435 c22475R_129_1 (by norm_num)

theorem hr22475R_129 : rows2 129 130 ≤ 2076806959546209 := rows2_le_of_rowsJ2 129 130 c22475R_129_0

theorem c22475R_130_1 : rowsJ2 130 131 46 300 ≤ 2078844632701216 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22475R_439 rows22475R_440 (by norm_num)

theorem c22475R_130_0 : rowsJ2 130 131 0 300 ≤ 2226619759593793 :=
  rowsJ2_le_of_split 130 131 (by norm_num) (by norm_num) rows22475R_438 c22475R_130_1 (by norm_num)

theorem hr22475R_130 : rows2 130 131 ≤ 2226619759593793 := rows2_le_of_rowsJ2 130 131 c22475R_130_0

theorem c22475R_131_1 : rowsJ2 131 132 45 300 ≤ 2239558108637017 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22475R_442 rows22475R_443 (by norm_num)

theorem c22475R_131_0 : rowsJ2 131 132 0 300 ≤ 2373711155381521 :=
  rowsJ2_le_of_split 131 132 (by norm_num) (by norm_num) rows22475R_441 c22475R_131_1 (by norm_num)

theorem hr22475R_131 : rows2 131 132 ≤ 2373711155381521 := rows2_le_of_rowsJ2 131 132 c22475R_131_0

theorem c22475R_132_1 : rowsJ2 132 133 45 300 ≤ 2375516200286590 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22475R_445 rows22475R_446 (by norm_num)

theorem c22475R_132_0 : rowsJ2 132 133 0 300 ≤ 2511232206498069 :=
  rowsJ2_le_of_split 132 133 (by norm_num) (by norm_num) rows22475R_444 c22475R_132_1 (by norm_num)

theorem hr22475R_132 : rows2 132 133 ≤ 2511232206498069 := rows2_le_of_rowsJ2 132 133 c22475R_132_0

theorem c22475R_133_1 : rowsJ2 133 134 45 300 ≤ 2519629310133730 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22475R_448 rows22475R_449 (by norm_num)

theorem c22475R_133_0 : rowsJ2 133 134 0 300 ≤ 2655594527133344 :=
  rowsJ2_le_of_split 133 134 (by norm_num) (by norm_num) rows22475R_447 c22475R_133_1 (by norm_num)

theorem hr22475R_133 : rows2 133 134 ≤ 2655594527133344 := rows2_le_of_rowsJ2 133 134 c22475R_133_0

theorem c22475R_134_1 : rowsJ2 134 135 44 300 ≤ 2526196450123402 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22475R_451 rows22475R_452 (by norm_num)

theorem c22475R_134_0 : rowsJ2 134 135 0 300 ≤ 2652040038161105 :=
  rowsJ2_le_of_split 134 135 (by norm_num) (by norm_num) rows22475R_450 c22475R_134_1 (by norm_num)

theorem hr22475R_134 : rows2 134 135 ≤ 2652040038161105 := rows2_le_of_rowsJ2 134 135 c22475R_134_0

theorem c22475R_135_1 : rowsJ2 135 136 44 300 ≤ 2511700223595260 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22475R_454 rows22475R_455 (by norm_num)

theorem c22475R_135_0 : rowsJ2 135 136 0 300 ≤ 2639190052152832 :=
  rowsJ2_le_of_split 135 136 (by norm_num) (by norm_num) rows22475R_453 c22475R_135_1 (by norm_num)

theorem hr22475R_135 : rows2 135 136 ≤ 2639190052152832 := rows2_le_of_rowsJ2 135 136 c22475R_135_0

theorem c22475R_136_1 : rowsJ2 136 137 44 300 ≤ 2506990123902699 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22475R_457 rows22475R_458 (by norm_num)

theorem c22475R_136_0 : rowsJ2 136 137 0 300 ≤ 2637944083421938 :=
  rowsJ2_le_of_split 136 137 (by norm_num) (by norm_num) rows22475R_456 c22475R_136_1 (by norm_num)

theorem hr22475R_136 : rows2 136 137 ≤ 2637944083421938 := rows2_le_of_rowsJ2 136 137 c22475R_136_0

theorem c22475R_137_0 : rowsJ2 137 138 0 300 ≤ 2637012543922780 :=
  rowsJ2_le_of_split 137 138 (by norm_num) (by norm_num) rows22475R_459 rows22475R_460 (by norm_num)

theorem hr22475R_137 : rows2 137 138 ≤ 2637012543922780 := rows2_le_of_rowsJ2 137 138 c22475R_137_0

theorem c22475R_138_0 : rowsJ2 138 139 0 300 ≤ 2628819835063014 :=
  rowsJ2_le_of_split 138 139 (by norm_num) (by norm_num) rows22475R_461 rows22475R_462 (by norm_num)

theorem hr22475R_138 : rows2 138 139 ≤ 2628819835063014 := rows2_le_of_rowsJ2 138 139 c22475R_138_0

theorem c22475R_139_0 : rowsJ2 139 140 0 300 ≤ 2630303475358383 :=
  rowsJ2_le_of_split 139 140 (by norm_num) (by norm_num) rows22475R_463 rows22475R_464 (by norm_num)

theorem hr22475R_139 : rows2 139 140 ≤ 2630303475358383 := rows2_le_of_rowsJ2 139 140 c22475R_139_0

theorem c22475R_140_0 : rowsJ2 140 141 0 300 ≤ 2633809064179716 :=
  rowsJ2_le_of_split 140 141 (by norm_num) (by norm_num) rows22475R_465 rows22475R_466 (by norm_num)

theorem hr22475R_140 : rows2 140 141 ≤ 2633809064179716 := rows2_le_of_rowsJ2 140 141 c22475R_140_0

theorem c22475R_141_0 : rowsJ2 141 142 0 300 ≤ 2628354791183629 :=
  rowsJ2_le_of_split 141 142 (by norm_num) (by norm_num) rows22475R_467 rows22475R_468 (by norm_num)

theorem hr22475R_141 : rows2 141 142 ≤ 2628354791183629 := rows2_le_of_rowsJ2 141 142 c22475R_141_0

theorem c22475R_142_0 : rowsJ2 142 143 0 300 ≤ 2634977550086778 :=
  rowsJ2_le_of_split 142 143 (by norm_num) (by norm_num) rows22475R_469 rows22475R_470 (by norm_num)

theorem hr22475R_142 : rows2 142 143 ≤ 2634977550086778 := rows2_le_of_rowsJ2 142 143 c22475R_142_0

theorem c22475R_143_0 : rowsJ2 143 144 0 300 ≤ 2643925126137598 :=
  rowsJ2_le_of_split 143 144 (by norm_num) (by norm_num) rows22475R_471 rows22475R_472 (by norm_num)

theorem hr22475R_143 : rows2 143 144 ≤ 2643925126137598 := rows2_le_of_rowsJ2 143 144 c22475R_143_0

theorem c22475R_144_0 : rowsJ2 144 145 0 300 ≤ 2647120696901234 :=
  rowsJ2_le_of_split 144 145 (by norm_num) (by norm_num) rows22475R_473 rows22475R_474 (by norm_num)

theorem hr22475R_144 : rows2 144 145 ≤ 2647120696901234 := rows2_le_of_rowsJ2 144 145 c22475R_144_0

theorem c22475R_145_0 : rowsJ2 145 146 0 300 ≤ 2661911318128589 :=
  rowsJ2_le_of_split 145 146 (by norm_num) (by norm_num) rows22475R_475 rows22475R_476 (by norm_num)

theorem hr22475R_145 : rows2 145 146 ≤ 2661911318128589 := rows2_le_of_rowsJ2 145 146 c22475R_145_0

theorem c22475R_146_0 : rowsJ2 146 147 0 300 ≤ 2680129843605761 :=
  rowsJ2_le_of_split 146 147 (by norm_num) (by norm_num) rows22475R_477 rows22475R_478 (by norm_num)

theorem hr22475R_146 : rows2 146 147 ≤ 2680129843605761 := rows2_le_of_rowsJ2 146 147 c22475R_146_0

theorem c22475R_147_0 : rowsJ2 147 148 0 300 ≤ 2691463371676501 :=
  rowsJ2_le_of_split 147 148 (by norm_num) (by norm_num) rows22475R_479 rows22475R_480 (by norm_num)

theorem hr22475R_147 : rows2 147 148 ≤ 2691463371676501 := rows2_le_of_rowsJ2 147 148 c22475R_147_0

theorem c22475R_148_0 : rowsJ2 148 149 0 300 ≤ 2704781614349264 :=
  rowsJ2_le_of_split 148 149 (by norm_num) (by norm_num) rows22475R_481 rows22475R_482 (by norm_num)

theorem hr22475R_148 : rows2 148 149 ≤ 2704781614349264 := rows2_le_of_rowsJ2 148 149 c22475R_148_0

theorem c22475R_149_0 : rowsJ2 149 150 0 300 ≤ 2718917906691744 :=
  rowsJ2_le_of_split 149 150 (by norm_num) (by norm_num) rows22475R_483 rows22475R_484 (by norm_num)

theorem hr22475R_149 : rows2 149 150 ≤ 2718917906691744 := rows2_le_of_rowsJ2 149 150 c22475R_149_0

theorem c22475R_150_0 : rowsJ2 150 151 0 300 ≤ 2735425931424409 :=
  rowsJ2_le_of_split 150 151 (by norm_num) (by norm_num) rows22475R_485 rows22475R_486 (by norm_num)

theorem hr22475R_150 : rows2 150 151 ≤ 2735425931424409 := rows2_le_of_rowsJ2 150 151 c22475R_150_0

theorem c22475R_151_0 : rowsJ2 151 152 0 300 ≤ 2753518184663816 :=
  rowsJ2_le_of_split 151 152 (by norm_num) (by norm_num) rows22475R_487 rows22475R_488 (by norm_num)

theorem hr22475R_151 : rows2 151 152 ≤ 2753518184663816 := rows2_le_of_rowsJ2 151 152 c22475R_151_0

theorem c22475R_152_0 : rowsJ2 152 153 0 300 ≤ 2773983714982518 :=
  rowsJ2_le_of_split 152 153 (by norm_num) (by norm_num) rows22475R_489 rows22475R_490 (by norm_num)

theorem hr22475R_152 : rows2 152 153 ≤ 2773983714982518 := rows2_le_of_rowsJ2 152 153 c22475R_152_0

theorem c22475R_153_0 : rowsJ2 153 154 0 300 ≤ 2795796004054335 :=
  rowsJ2_le_of_split 153 154 (by norm_num) (by norm_num) rows22475R_491 rows22475R_492 (by norm_num)

theorem hr22475R_153 : rows2 153 154 ≤ 2795796004054335 := rows2_le_of_rowsJ2 153 154 c22475R_153_0

theorem c22475R_154_0 : rowsJ2 154 155 0 300 ≤ 2820082470945485 :=
  rowsJ2_le_of_split 154 155 (by norm_num) (by norm_num) rows22475R_493 rows22475R_494 (by norm_num)

theorem hr22475R_154 : rows2 154 155 ≤ 2820082470945485 := rows2_le_of_rowsJ2 154 155 c22475R_154_0

theorem t22475R_169 : rows2 294 300 ≤ 88923706700618085 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_532 rows22475R_533 (by norm_num)

theorem t22475R_168 : rows2 290 300 ≤ 142899122260904546 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_531 t22475R_169 (by norm_num)

theorem t22475R_167 : rows2 286 300 ≤ 193200539248369595 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_530 t22475R_168 (by norm_num)

theorem t22475R_166 : rows2 236 300 ≤ 236334678681256856 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_529 t22475R_167 (by norm_num)

theorem t22475R_165 : rows2 232 300 ≤ 279161197284178360 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_528 t22475R_166 (by norm_num)

theorem t22475R_164 : rows2 228 300 ≤ 321619598877339272 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_527 t22475R_165 (by norm_num)

theorem t22475R_163 : rows2 225 300 ≤ 353139025128501849 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_526 t22475R_164 (by norm_num)

theorem t22475R_162 : rows2 222 300 ≤ 384537708209848552 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_525 t22475R_163 (by norm_num)

theorem t22475R_161 : rows2 219 300 ≤ 415567811388422331 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_524 t22475R_162 (by norm_num)

theorem t22475R_160 : rows2 216 300 ≤ 446451523828435763 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_523 t22475R_161 (by norm_num)

theorem t22475R_159 : rows2 213 300 ≤ 476974183807911139 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_522 t22475R_160 (by norm_num)

theorem t22475R_158 : rows2 210 300 ≤ 507111791556107685 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_521 t22475R_159 (by norm_num)

theorem t22475R_157 : rows2 207 300 ≤ 535926758973514093 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_520 t22475R_158 (by norm_num)

theorem t22475R_156 : rows2 204 300 ≤ 563456565080328319 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_519 t22475R_157 (by norm_num)

theorem t22475R_155 : rows2 201 300 ≤ 589856339114229555 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_518 t22475R_156 (by norm_num)

theorem t22475R_154 : rows2 198 300 ≤ 615140453799907542 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_517 t22475R_155 (by norm_num)

theorem t22475R_153 : rows2 195 300 ≤ 639444018907194107 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_516 t22475R_154 (by norm_num)

theorem t22475R_152 : rows2 191 300 ≤ 670366050158340903 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_515 t22475R_153 (by norm_num)

theorem t22475R_151 : rows2 187 300 ≤ 699819922179297516 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_514 t22475R_152 (by norm_num)

theorem t22475R_150 : rows2 183 300 ≤ 727908602482671597 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_513 t22475R_151 (by norm_num)

theorem t22475R_149 : rows2 179 300 ≤ 753669162088684626 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_512 t22475R_150 (by norm_num)

theorem t22475R_148 : rows2 176 300 ≤ 771410298655435744 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_511 t22475R_149 (by norm_num)

theorem t22475R_147 : rows2 173 300 ≤ 787863796690011660 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_510 t22475R_148 (by norm_num)

theorem t22475R_146 : rows2 171 300 ≤ 798146276975211158 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_509 t22475R_147 (by norm_num)

theorem t22475R_145 : rows2 169 300 ≤ 807901347497041543 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_508 t22475R_146 (by norm_num)

theorem t22475R_144 : rows2 167 300 ≤ 817140498520826431 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_507 t22475R_145 (by norm_num)

theorem t22475R_143 : rows2 166 300 ≤ 821565627111238178 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_506 t22475R_144 (by norm_num)

theorem t22475R_142 : rows2 165 300 ≤ 825855693832137502 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_505 t22475R_143 (by norm_num)

theorem t22475R_141 : rows2 164 300 ≤ 830008720005273329 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_504 t22475R_142 (by norm_num)

theorem t22475R_140 : rows2 163 300 ≤ 834019884091131220 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_503 t22475R_141 (by norm_num)

theorem t22475R_139 : rows2 162 300 ≤ 837887233114696073 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_502 t22475R_140 (by norm_num)

theorem t22475R_138 : rows2 161 300 ≤ 841606472582982650 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_501 t22475R_139 (by norm_num)

theorem t22475R_137 : rows2 160 300 ≤ 845175929030080925 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_500 t22475R_138 (by norm_num)

theorem t22475R_136 : rows2 159 300 ≤ 848591637264466389 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_499 t22475R_137 (by norm_num)

theorem t22475R_135 : rows2 158 300 ≤ 851851985529852021 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_498 t22475R_136 (by norm_num)

theorem t22475R_134 : rows2 157 300 ≤ 854953396310208669 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_497 t22475R_135 (by norm_num)

theorem t22475R_133 : rows2 156 300 ≤ 857894178788332903 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_496 t22475R_134 (by norm_num)

theorem t22475R_132 : rows2 155 300 ≤ 860739627734436887 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_495 t22475R_133 (by norm_num)

theorem t22475R_131 : rows2 154 300 ≤ 863559710205382372 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_154 t22475R_132 (by norm_num)

theorem t22475R_130 : rows2 153 300 ≤ 866355506209436707 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_153 t22475R_131 (by norm_num)

theorem t22475R_129 : rows2 152 300 ≤ 869129489924419225 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_152 t22475R_130 (by norm_num)

theorem t22475R_128 : rows2 151 300 ≤ 871883008109083041 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_151 t22475R_129 (by norm_num)

theorem t22475R_127 : rows2 150 300 ≤ 874618434040507450 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_150 t22475R_128 (by norm_num)

theorem t22475R_126 : rows2 149 300 ≤ 877337351947199194 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_149 t22475R_127 (by norm_num)

theorem t22475R_125 : rows2 148 300 ≤ 880042133561548458 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_148 t22475R_126 (by norm_num)

theorem t22475R_124 : rows2 147 300 ≤ 882733596933224959 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_147 t22475R_125 (by norm_num)

theorem t22475R_123 : rows2 146 300 ≤ 885413726776830720 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_146 t22475R_124 (by norm_num)

theorem t22475R_122 : rows2 145 300 ≤ 888075638094959309 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_145 t22475R_123 (by norm_num)

theorem t22475R_121 : rows2 144 300 ≤ 890722758791860543 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_144 t22475R_122 (by norm_num)

theorem t22475R_120 : rows2 143 300 ≤ 893366683917998141 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_143 t22475R_121 (by norm_num)

theorem t22475R_119 : rows2 142 300 ≤ 896001661468084919 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_142 t22475R_120 (by norm_num)

theorem t22475R_118 : rows2 141 300 ≤ 898630016259268548 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_141 t22475R_119 (by norm_num)

theorem t22475R_117 : rows2 140 300 ≤ 901263825323448264 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_140 t22475R_118 (by norm_num)

theorem t22475R_116 : rows2 139 300 ≤ 903894128798806647 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_139 t22475R_117 (by norm_num)

theorem t22475R_115 : rows2 138 300 ≤ 906522948633869661 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_138 t22475R_116 (by norm_num)

theorem t22475R_114 : rows2 137 300 ≤ 909159961177792441 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_137 t22475R_115 (by norm_num)

theorem t22475R_113 : rows2 136 300 ≤ 911797905261214379 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_136 t22475R_114 (by norm_num)

theorem t22475R_112 : rows2 135 300 ≤ 914437095313367211 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_135 t22475R_113 (by norm_num)

theorem t22475R_111 : rows2 134 300 ≤ 917089135351528316 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_134 t22475R_112 (by norm_num)

theorem t22475R_110 : rows2 133 300 ≤ 919744729878661660 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_133 t22475R_111 (by norm_num)

theorem t22475R_109 : rows2 132 300 ≤ 922255962085159729 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_132 t22475R_110 (by norm_num)

theorem t22475R_108 : rows2 131 300 ≤ 924629673240541250 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_131 t22475R_109 (by norm_num)

theorem t22475R_107 : rows2 130 300 ≤ 926856293000135043 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_130 t22475R_108 (by norm_num)

theorem t22475R_106 : rows2 129 300 ≤ 928933099959681252 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_129 t22475R_107 (by norm_num)

theorem t22475R_105 : rows2 128 300 ≤ 930869484182914266 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_128 t22475R_106 (by norm_num)

theorem t22475R_104 : rows2 127 300 ≤ 932653014263063727 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_127 t22475R_105 (by norm_num)

theorem t22475R_103 : rows2 126 300 ≤ 934283657299033675 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_126 t22475R_104 (by norm_num)

theorem t22475R_102 : rows2 125 300 ≤ 935747802092039732 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_125 t22475R_103 (by norm_num)

theorem t22475R_101 : rows2 124 300 ≤ 937043807287314995 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_124 t22475R_102 (by norm_num)

theorem t22475R_100 : rows2 123 300 ≤ 938167005725722607 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_123 t22475R_101 (by norm_num)

theorem t22475R_99 : rows2 122 300 ≤ 939232466601339701 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_122 t22475R_100 (by norm_num)

theorem t22475R_98 : rows2 121 300 ≤ 940117199141066700 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_121 t22475R_99 (by norm_num)

theorem t22475R_97 : rows2 120 300 ≤ 940932031375494185 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_120 t22475R_98 (by norm_num)

theorem t22475R_96 : rows2 119 300 ≤ 941557915261886740 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_119 t22475R_97 (by norm_num)

theorem t22475R_95 : rows2 118 300 ≤ 942203876683111816 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_118 t22475R_96 (by norm_num)

theorem t22475R_94 : rows2 117 300 ≤ 942861750998254880 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_117 t22475R_95 (by norm_num)

theorem t22475R_93 : rows2 116 300 ≤ 943641437433316580 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_116 t22475R_94 (by norm_num)

theorem t22475R_92 : rows2 115 300 ≤ 944434433856414902 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_115 t22475R_93 (by norm_num)

theorem t22475R_91 : rows2 114 300 ≤ 945349723173800730 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_114 t22475R_92 (by norm_num)

theorem t22475R_90 : rows2 113 300 ≤ 946278438193880575 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_113 t22475R_91 (by norm_num)

theorem t22475R_89 : rows2 112 300 ≤ 947328652398627497 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_112 t22475R_90 (by norm_num)

theorem t22475R_88 : rows2 111 300 ≤ 948392099219960400 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_111 t22475R_89 (by norm_num)

theorem t22475R_87 : rows2 110 300 ≤ 949577790017216968 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_110 t22475R_88 (by norm_num)

theorem t22475R_86 : rows2 109 300 ≤ 950778855005135738 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_109 t22475R_87 (by norm_num)

theorem t22475R_85 : rows2 108 300 ≤ 952106408464161353 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_108 t22475R_86 (by norm_num)

theorem t22475R_84 : rows2 107 300 ≤ 953454164521530048 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_107 t22475R_85 (by norm_num)

theorem t22475R_83 : rows2 106 300 ≤ 954934277646920449 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_106 t22475R_84 (by norm_num)

theorem t22475R_82 : rows2 105 300 ≤ 956439082894573654 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_105 t22475R_83 (by norm_num)

theorem t22475R_81 : rows2 104 300 ≤ 958081269241195804 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_104 t22475R_82 (by norm_num)

theorem t22475R_80 : rows2 103 300 ≤ 959751394850646697 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_103 t22475R_81 (by norm_num)

theorem t22475R_79 : rows2 102 300 ≤ 961564674657468846 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_102 t22475R_80 (by norm_num)

theorem t22475R_78 : rows2 101 300 ≤ 963409849478961885 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_101 t22475R_79 (by norm_num)

theorem t22475R_77 : rows2 100 300 ≤ 965404137037631785 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_100 t22475R_78 (by norm_num)

theorem t22475R_76 : rows2 99 300 ≤ 967434499683958068 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_99 t22475R_77 (by norm_num)

theorem t22475R_75 : rows2 98 300 ≤ 969620374203552637 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_98 t22475R_76 (by norm_num)

theorem t22475R_74 : rows2 97 300 ≤ 971846002806133668 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_97 t22475R_75 (by norm_num)

theorem t22475R_73 : rows2 96 300 ≤ 974163469801352065 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_96 t22475R_74 (by norm_num)

theorem t22475R_72 : rows2 95 300 ≤ 976293464007153798 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_95 t22475R_73 (by norm_num)

theorem t22475R_71 : rows2 94 300 ≤ 978352551840985454 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_94 t22475R_72 (by norm_num)

theorem t22475R_70 : rows2 93 300 ≤ 980211951734085111 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_93 t22475R_71 (by norm_num)

theorem t22475R_69 : rows2 92 300 ≤ 981990533326425522 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_92 t22475R_70 (by norm_num)

theorem t22475R_68 : rows2 91 300 ≤ 983556280227103090 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_91 t22475R_69 (by norm_num)

theorem t22475R_67 : rows2 90 300 ≤ 985030989038696869 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_90 t22475R_68 (by norm_num)

theorem t22475R_66 : rows2 89 300 ≤ 986279832595531928 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_89 t22475R_67 (by norm_num)

theorem t22475R_65 : rows2 88 300 ≤ 987426951442754554 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_88 t22475R_66 (by norm_num)

theorem t22475R_64 : rows2 87 300 ≤ 988422069566575588 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_87 t22475R_65 (by norm_num)

theorem t22475R_63 : rows2 86 300 ≤ 989445636156544373 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_86 t22475R_64 (by norm_num)

theorem t22475R_62 : rows2 85 300 ≤ 990500621222318776 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_85 t22475R_63 (by norm_num)

theorem t22475R_61 : rows2 84 300 ≤ 991595247658341604 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_84 t22475R_62 (by norm_num)

theorem t22475R_60 : rows2 83 300 ≤ 992732030314885904 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_83 t22475R_61 (by norm_num)

theorem t22475R_59 : rows2 82 300 ≤ 993918187172856971 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_82 t22475R_60 (by norm_num)

theorem t22475R_58 : rows2 81 300 ≤ 995155754777912657 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_81 t22475R_59 (by norm_num)

theorem t22475R_57 : rows2 80 300 ≤ 996450641146010810 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_80 t22475R_58 (by norm_num)

theorem t22475R_56 : rows2 79 300 ≤ 997803256587664962 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_79 t22475R_57 (by norm_num)

theorem t22475R_55 : rows2 78 300 ≤ 999218406008800173 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_78 t22475R_56 (by norm_num)

theorem t22475R_54 : rows2 77 300 ≤ 1000695276708619260 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_77 t22475R_55 (by norm_num)

theorem t22475R_53 : rows2 76 300 ≤ 1002237416373249914 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_76 t22475R_54 (by norm_num)

theorem t22475R_52 : rows2 75 300 ≤ 1003843896566775948 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_75 t22475R_53 (by norm_num)

theorem t22475R_51 : rows2 74 300 ≤ 1005517973308216819 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_74 t22475R_52 (by norm_num)

theorem t22475R_50 : rows2 73 300 ≤ 1007258107655557378 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_73 t22475R_51 (by norm_num)

theorem t22475R_49 : rows2 72 300 ≤ 1009066762957961461 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_72 t22475R_50 (by norm_num)

theorem t22475R_48 : rows2 71 300 ≤ 1010942179558367832 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_71 t22475R_49 (by norm_num)

theorem t22475R_47 : rows2 70 300 ≤ 1012885723561518928 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_70 t22475R_48 (by norm_num)

theorem t22475R_46 : rows2 69 300 ≤ 1014894275598937942 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_69 t22475R_47 (by norm_num)

theorem t22475R_45 : rows2 68 300 ≤ 1016967776263212721 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_68 t22475R_46 (by norm_num)

theorem t22475R_44 : rows2 67 300 ≤ 1019101781095505890 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_67 t22475R_45 (by norm_num)

theorem t22475R_43 : rows2 66 300 ≤ 1021295652104775268 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_66 t22475R_44 (by norm_num)

theorem t22475R_42 : rows2 65 300 ≤ 1023544222461877490 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_65 t22475R_43 (by norm_num)

theorem t22475R_41 : rows2 64 300 ≤ 1025845966138741924 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_64 t22475R_42 (by norm_num)

theorem t22475R_40 : rows2 63 300 ≤ 1028195417867324242 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_63 t22475R_41 (by norm_num)

theorem t22475R_39 : rows2 62 300 ≤ 1030590527381486905 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_62 t22475R_40 (by norm_num)

theorem t22475R_38 : rows2 61 300 ≤ 1033025189835482877 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_61 t22475R_39 (by norm_num)

theorem t22475R_37 : rows2 60 300 ≤ 1035497358874182966 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_60 t22475R_38 (by norm_num)

theorem t22475R_36 : rows2 59 300 ≤ 1038000784222617099 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_59 t22475R_37 (by norm_num)

theorem t22475R_35 : rows2 58 300 ≤ 1040533352989471619 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_58 t22475R_36 (by norm_num)

theorem t22475R_34 : rows2 57 300 ≤ 1043089603423945892 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_57 t22475R_35 (by norm_num)

theorem t22475R_33 : rows2 56 300 ≤ 1045668016083013690 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_56 t22475R_34 (by norm_num)

theorem t22475R_32 : rows2 55 300 ≤ 1048263468662176779 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_55 t22475R_33 (by norm_num)

theorem t22475R_31 : rows2 54 300 ≤ 1050875183034908384 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_54 t22475R_32 (by norm_num)

theorem t22475R_30 : rows2 53 300 ≤ 1053498517959153347 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_53 t22475R_31 (by norm_num)

theorem t22475R_29 : rows2 52 300 ≤ 1056132922776651484 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_52 t22475R_30 (by norm_num)

theorem t22475R_28 : rows2 51 300 ≤ 1058774392546642927 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_51 t22475R_29 (by norm_num)

theorem t22475R_27 : rows2 50 300 ≤ 1061422760581985170 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_50 t22475R_28 (by norm_num)

theorem t22475R_26 : rows2 49 300 ≤ 1064073689093127554 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_49 t22475R_27 (by norm_num)

theorem t22475R_25 : rows2 48 300 ≤ 1066725168960032153 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_48 t22475R_26 (by norm_num)

theorem t22475R_24 : rows2 47 300 ≤ 1069386962126176233 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_47 t22475R_25 (by norm_num)

theorem t22475R_23 : rows2 46 300 ≤ 1072072166011732283 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_46 t22475R_24 (by norm_num)

theorem t22475R_22 : rows2 45 300 ≤ 1074791618671556989 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_45 t22475R_23 (by norm_num)

theorem t22475R_21 : rows2 44 300 ≤ 1077553051820148363 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_44 t22475R_22 (by norm_num)

theorem t22475R_20 : rows2 43 300 ≤ 1080361908462131125 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_43 t22475R_21 (by norm_num)

theorem t22475R_19 : rows2 42 300 ≤ 1083221279410636433 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_42 t22475R_20 (by norm_num)

theorem t22475R_18 : rows2 41 300 ≤ 1086131522893852763 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_41 t22475R_19 (by norm_num)

theorem t22475R_17 : rows2 40 300 ≤ 1089089907651020822 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_40 t22475R_18 (by norm_num)

theorem t22475R_16 : rows2 39 300 ≤ 1092091218094109022 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_39 t22475R_17 (by norm_num)

theorem t22475R_15 : rows2 38 300 ≤ 1095126993772048250 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_38 t22475R_16 (by norm_num)

theorem t22475R_14 : rows2 37 300 ≤ 1098186230901490698 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_37 t22475R_15 (by norm_num)

theorem t22475R_13 : rows2 36 300 ≤ 1101255085713670975 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_36 t22475R_14 (by norm_num)

theorem t22475R_12 : rows2 35 300 ≤ 1104316892809836480 :=
  rows2_le_of_split (by norm_num) (by norm_num) hr22475R_35 t22475R_13 (by norm_num)

theorem t22475R_11 : rows2 34 300 ≤ 1107352088918132458 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_11 t22475R_12 (by norm_num)

theorem t22475R_10 : rows2 33 300 ≤ 1110339529897411299 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_10 t22475R_11 (by norm_num)

theorem t22475R_9 : rows2 32 300 ≤ 1113256419384304482 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_9 t22475R_10 (by norm_num)

theorem t22475R_8 : rows2 31 300 ≤ 1116082547038739312 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_8 t22475R_9 (by norm_num)

theorem t22475R_7 : rows2 30 300 ≤ 1118801252271129885 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_7 t22475R_8 (by norm_num)

theorem t22475R_6 : rows2 29 300 ≤ 1121398944798031279 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_6 t22475R_7 (by norm_num)

theorem t22475R_5 : rows2 28 300 ≤ 1123865176641283896 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_5 t22475R_6 (by norm_num)

theorem t22475R_4 : rows2 27 300 ≤ 1126192513860522371 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_4 t22475R_5 (by norm_num)

theorem t22475R_3 : rows2 25 300 ≤ 1130414379971060068 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_3 t22475R_4 (by norm_num)

theorem t22475R_2 : rows2 23 300 ≤ 1134060253272716285 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_2 t22475R_3 (by norm_num)

theorem t22475R_1 : rows2 19 300 ≤ 1139731578165392717 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_1 t22475R_2 (by norm_num)

theorem t22475R_0 : rows2 0 300 ≤ 1146984490308086981 :=
  rows2_le_of_split (by norm_num) (by norm_num) rows22475R_0 t22475R_1 (by norm_num)

/-- **The refined certificate on `grid22475R`**: the loss's bound is less than `K`, the 534 parts checked by the
kernel. -/
theorem total2_lt_22475R : total2 < K := by
  rw [total2_eq_rows2_full]
  exact lt_of_le_of_lt t22475R_0 (by decide +kernel)

end

end SieveCert

#print axioms SieveCert.total2_lt_22475R
