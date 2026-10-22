/-
# Round 625: the certificate of the sieve route's loss at `L = 9/4` (under `CGLDensity` alone): `total < K`

On `SieveGrid225C.grid225C` (`U1 = ⌈(41191/100000)DEN⌉`, `U2 = ⌊(48127/100000)DEN⌋`, `n = 400`), `SieveCert.total` is
less than `K`, the form round 619's `SieveMain.linnik_route_lt` takes (the total is below `0.98921K`; round 632: it
read "the total is `0.989K`", rounded down; review of round 625, F5): the total is `rows 0 n`
(`SieveCertCols.total_eq_rows_full`), and its bound is assembled one step at a time from the 1374 parts' bounds
(`rows225C_0` … `rows225C_1373`, each by `decide +kernel` in one of the 167 part files): a heavy row's bound from its
column pieces' (`rowsJ_le_of_split`, `rows_le_of_rowsJ`; `rowsJ`, `SieveCertColsDefs.lean`), then the 211 ranges of
rows from the last to the first (`rows_le_of_split`), every bound a literal and every step a theorem of its own
(`c…`, `hr…`, `t…`); the bounds, `⌈1.001 × part⌉` computed exactly in integers, sum to
`1141621279451627817`, less than `K` by `decide +kernel` (`total_lt_225C`).

The file imports `SieveCertCols.lean` and `SieveCert225CP1.lean` … `SieveCert225CP167.lean`.
-/
import SieveCertCols
import SieveCert225CP1
import SieveCert225CP2
import SieveCert225CP3
import SieveCert225CP4
import SieveCert225CP5
import SieveCert225CP6
import SieveCert225CP7
import SieveCert225CP8
import SieveCert225CP9
import SieveCert225CP10
import SieveCert225CP11
import SieveCert225CP12
import SieveCert225CP13
import SieveCert225CP14
import SieveCert225CP15
import SieveCert225CP16
import SieveCert225CP17
import SieveCert225CP18
import SieveCert225CP19
import SieveCert225CP20
import SieveCert225CP21
import SieveCert225CP22
import SieveCert225CP23
import SieveCert225CP24
import SieveCert225CP25
import SieveCert225CP26
import SieveCert225CP27
import SieveCert225CP28
import SieveCert225CP29
import SieveCert225CP30
import SieveCert225CP31
import SieveCert225CP32
import SieveCert225CP33
import SieveCert225CP34
import SieveCert225CP35
import SieveCert225CP36
import SieveCert225CP37
import SieveCert225CP38
import SieveCert225CP39
import SieveCert225CP40
import SieveCert225CP41
import SieveCert225CP42
import SieveCert225CP43
import SieveCert225CP44
import SieveCert225CP45
import SieveCert225CP46
import SieveCert225CP47
import SieveCert225CP48
import SieveCert225CP49
import SieveCert225CP50
import SieveCert225CP51
import SieveCert225CP52
import SieveCert225CP53
import SieveCert225CP54
import SieveCert225CP55
import SieveCert225CP56
import SieveCert225CP57
import SieveCert225CP58
import SieveCert225CP59
import SieveCert225CP60
import SieveCert225CP61
import SieveCert225CP62
import SieveCert225CP63
import SieveCert225CP64
import SieveCert225CP65
import SieveCert225CP66
import SieveCert225CP67
import SieveCert225CP68
import SieveCert225CP69
import SieveCert225CP70
import SieveCert225CP71
import SieveCert225CP72
import SieveCert225CP73
import SieveCert225CP74
import SieveCert225CP75
import SieveCert225CP76
import SieveCert225CP77
import SieveCert225CP78
import SieveCert225CP79
import SieveCert225CP80
import SieveCert225CP81
import SieveCert225CP82
import SieveCert225CP83
import SieveCert225CP84
import SieveCert225CP85
import SieveCert225CP86
import SieveCert225CP87
import SieveCert225CP88
import SieveCert225CP89
import SieveCert225CP90
import SieveCert225CP91
import SieveCert225CP92
import SieveCert225CP93
import SieveCert225CP94
import SieveCert225CP95
import SieveCert225CP96
import SieveCert225CP97
import SieveCert225CP98
import SieveCert225CP99
import SieveCert225CP100
import SieveCert225CP101
import SieveCert225CP102
import SieveCert225CP103
import SieveCert225CP104
import SieveCert225CP105
import SieveCert225CP106
import SieveCert225CP107
import SieveCert225CP108
import SieveCert225CP109
import SieveCert225CP110
import SieveCert225CP111
import SieveCert225CP112
import SieveCert225CP113
import SieveCert225CP114
import SieveCert225CP115
import SieveCert225CP116
import SieveCert225CP117
import SieveCert225CP118
import SieveCert225CP119
import SieveCert225CP120
import SieveCert225CP121
import SieveCert225CP122
import SieveCert225CP123
import SieveCert225CP124
import SieveCert225CP125
import SieveCert225CP126
import SieveCert225CP127
import SieveCert225CP128
import SieveCert225CP129
import SieveCert225CP130
import SieveCert225CP131
import SieveCert225CP132
import SieveCert225CP133
import SieveCert225CP134
import SieveCert225CP135
import SieveCert225CP136
import SieveCert225CP137
import SieveCert225CP138
import SieveCert225CP139
import SieveCert225CP140
import SieveCert225CP141
import SieveCert225CP142
import SieveCert225CP143
import SieveCert225CP144
import SieveCert225CP145
import SieveCert225CP146
import SieveCert225CP147
import SieveCert225CP148
import SieveCert225CP149
import SieveCert225CP150
import SieveCert225CP151
import SieveCert225CP152
import SieveCert225CP153
import SieveCert225CP154
import SieveCert225CP155
import SieveCert225CP156
import SieveCert225CP157
import SieveCert225CP158
import SieveCert225CP159
import SieveCert225CP160
import SieveCert225CP161
import SieveCert225CP162
import SieveCert225CP163
import SieveCert225CP164
import SieveCert225CP165
import SieveCert225CP166
import SieveCert225CP167

namespace SieveCert

section

attribute [local instance] grid225C

/-! The chain of bounds: `c{i}_{m}` for the heavy row `i` from its `m`-th column piece on, `hr{i}` for the
heavy row `i`, `t{m}` for the rows from the `m`-th range on; each a theorem of its own. -/

theorem c35_0 : rowsJ 35 36 0 400 ≤ 1369426769704026 :=
  rowsJ_le_of_split 35 36 (by norm_num) (by norm_num) rows225C_12 rows225C_13 (by norm_num)

theorem hr35 : rows 35 36 ≤ 1369426769704026 := rows_le_of_rowsJ 35 36 c35_0

theorem c36_0 : rowsJ 36 37 0 400 ≤ 1432180015418123 :=
  rowsJ_le_of_split 36 37 (by norm_num) (by norm_num) rows225C_14 rows225C_15 (by norm_num)

theorem hr36 : rows 36 37 ≤ 1432180015418123 := rows_le_of_rowsJ 36 37 c36_0

theorem c37_0 : rowsJ 37 38 0 400 ≤ 1491431822772994 :=
  rowsJ_le_of_split 37 38 (by norm_num) (by norm_num) rows225C_16 rows225C_17 (by norm_num)

theorem hr37 : rows 37 38 ≤ 1491431822772994 := rows_le_of_rowsJ 37 38 c37_0

theorem c38_0 : rowsJ 38 39 0 400 ≤ 1546223477773982 :=
  rowsJ_le_of_split 38 39 (by norm_num) (by norm_num) rows225C_18 rows225C_19 (by norm_num)

theorem hr38 : rows 38 39 ≤ 1546223477773982 := rows_le_of_rowsJ 38 39 c38_0

theorem c39_0 : rowsJ 39 40 0 400 ≤ 1595642092773973 :=
  rowsJ_le_of_split 39 40 (by norm_num) (by norm_num) rows225C_20 rows225C_21 (by norm_num)

theorem hr39 : rows 39 40 ≤ 1595642092773973 := rows_le_of_rowsJ 39 40 c39_0

theorem c40_0 : rowsJ 40 41 0 400 ≤ 1638656445526546 :=
  rowsJ_le_of_split 40 41 (by norm_num) (by norm_num) rows225C_22 rows225C_23 (by norm_num)

theorem hr40 : rows 40 41 ≤ 1638656445526546 := rows_le_of_rowsJ 40 41 c40_0

theorem c41_0 : rowsJ 41 42 0 400 ≤ 1674185185561289 :=
  rowsJ_le_of_split 41 42 (by norm_num) (by norm_num) rows225C_24 rows225C_25 (by norm_num)

theorem hr41 : rows 41 42 ≤ 1674185185561289 := rows_le_of_rowsJ 41 42 c41_0

theorem c42_0 : rowsJ 42 43 0 400 ≤ 1701290331176072 :=
  rowsJ_le_of_split 42 43 (by norm_num) (by norm_num) rows225C_26 rows225C_27 (by norm_num)

theorem hr42 : rows 42 43 ≤ 1701290331176072 := rows_le_of_rowsJ 42 43 c42_0

theorem c43_0 : rowsJ 43 44 0 400 ≤ 1720028712573259 :=
  rowsJ_le_of_split 43 44 (by norm_num) (by norm_num) rows225C_28 rows225C_29 (by norm_num)

theorem hr43 : rows 43 44 ≤ 1720028712573259 := rows_le_of_rowsJ 43 44 c43_0

theorem c44_1 : rowsJ 44 45 35 400 ≤ 573299011878804 :=
  rowsJ_le_of_split 44 45 (by norm_num) (by norm_num) rows225C_31 rows225C_32 (by norm_num)

theorem c44_0 : rowsJ 44 45 0 400 ≤ 1730939396127439 :=
  rowsJ_le_of_split 44 45 (by norm_num) (by norm_num) rows225C_30 c44_1 (by norm_num)

theorem hr44 : rows 44 45 ≤ 1730939396127439 := rows_le_of_rowsJ 44 45 c44_0

theorem c45_1 : rowsJ 45 46 35 400 ≤ 591995089351148 :=
  rowsJ_le_of_split 45 46 (by norm_num) (by norm_num) rows225C_34 rows225C_35 (by norm_num)

theorem c45_0 : rowsJ 45 46 0 400 ≤ 1734506024584166 :=
  rowsJ_le_of_split 45 46 (by norm_num) (by norm_num) rows225C_33 c45_1 (by norm_num)

theorem hr45 : rows 45 46 ≤ 1734506024584166 := rows_le_of_rowsJ 45 46 c45_0

theorem c46_1 : rowsJ 46 47 35 400 ≤ 604032215218762 :=
  rowsJ_le_of_split 46 47 (by norm_num) (by norm_num) rows225C_37 rows225C_38 (by norm_num)

theorem c46_0 : rowsJ 46 47 0 400 ≤ 1731246958911908 :=
  rowsJ_le_of_split 46 47 (by norm_num) (by norm_num) rows225C_36 c46_1 (by norm_num)

theorem hr46 : rows 46 47 ≤ 1731246958911908 := rows_le_of_rowsJ 46 47 c46_0

theorem c47_1 : rowsJ 47 48 35 400 ≤ 610036301374981 :=
  rowsJ_le_of_split 47 48 (by norm_num) (by norm_num) rows225C_40 rows225C_41 (by norm_num)

theorem c47_0 : rowsJ 47 48 0 400 ≤ 1721691706241889 :=
  rowsJ_le_of_split 47 48 (by norm_num) (by norm_num) rows225C_39 c47_1 (by norm_num)

theorem hr47 : rows 47 48 ≤ 1721691706241889 := rows_le_of_rowsJ 47 48 c47_0

theorem c48_1 : rowsJ 48 49 35 400 ≤ 610917394217828 :=
  rowsJ_le_of_split 48 49 (by norm_num) (by norm_num) rows225C_43 rows225C_44 (by norm_num)

theorem c48_0 : rowsJ 48 49 0 400 ≤ 1706820764868974 :=
  rowsJ_le_of_split 48 49 (by norm_num) (by norm_num) rows225C_42 c48_1 (by norm_num)

theorem hr48 : rows 48 49 ≤ 1706820764868974 := rows_le_of_rowsJ 48 49 c48_0

theorem c49_1 : rowsJ 49 50 35 400 ≤ 607505712012075 :=
  rowsJ_le_of_split 49 50 (by norm_num) (by norm_num) rows225C_46 rows225C_47 (by norm_num)

theorem c49_0 : rowsJ 49 50 0 400 ≤ 1687365875355449 :=
  rowsJ_le_of_split 49 50 (by norm_num) (by norm_num) rows225C_45 c49_1 (by norm_num)

theorem hr49 : rows 49 50 ≤ 1687365875355449 := rows_le_of_rowsJ 49 50 c49_0

theorem c50_2 : rowsJ 50 51 44 400 ≤ 199119050311837 :=
  rowsJ_le_of_split 50 51 (by norm_num) (by norm_num) rows225C_50 rows225C_51 (by norm_num)

theorem c50_1 : rowsJ 50 51 35 400 ≤ 600703160769280 :=
  rowsJ_le_of_split 50 51 (by norm_num) (by norm_num) rows225C_49 c50_2 (by norm_num)

theorem c50_0 : rowsJ 50 51 0 400 ≤ 1664216885688208 :=
  rowsJ_le_of_split 50 51 (by norm_num) (by norm_num) rows225C_48 c50_1 (by norm_num)

theorem hr50 : rows 50 51 ≤ 1664216885688208 := rows_le_of_rowsJ 50 51 c50_0

theorem c51_2 : rowsJ 51 52 44 400 ≤ 209971928914501 :=
  rowsJ_le_of_split 51 52 (by norm_num) (by norm_num) rows225C_54 rows225C_55 (by norm_num)

theorem c51_1 : rowsJ 51 52 35 400 ≤ 591375956850334 :=
  rowsJ_le_of_split 51 52 (by norm_num) (by norm_num) rows225C_53 c51_2 (by norm_num)

theorem c51_0 : rowsJ 51 52 0 400 ≤ 1638221919630601 :=
  rowsJ_le_of_split 51 52 (by norm_num) (by norm_num) rows225C_52 c51_1 (by norm_num)

theorem hr51 : rows 51 52 ≤ 1638221919630601 := rows_le_of_rowsJ 51 52 c51_0

theorem c52_2 : rowsJ 52 53 44 400 ≤ 218873462683207 :=
  rowsJ_le_of_split 52 53 (by norm_num) (by norm_num) rows225C_58 rows225C_59 (by norm_num)

theorem c52_1 : rowsJ 52 53 35 400 ≤ 580394250459230 :=
  rowsJ_le_of_split 52 53 (by norm_num) (by norm_num) rows225C_57 c52_2 (by norm_num)

theorem c52_0 : rowsJ 52 53 0 400 ≤ 1610238184174088 :=
  rowsJ_le_of_split 52 53 (by norm_num) (by norm_num) rows225C_56 c52_1 (by norm_num)

theorem hr52 : rows 52 53 ≤ 1610238184174088 := rows_le_of_rowsJ 52 53 c52_0

theorem c53_2 : rowsJ 53 54 44 400 ≤ 226618832976235 :=
  rowsJ_le_of_split 53 54 (by norm_num) (by norm_num) rows225C_62 rows225C_63 (by norm_num)

theorem c53_1 : rowsJ 53 54 35 400 ≤ 568637512803768 :=
  rowsJ_le_of_split 53 54 (by norm_num) (by norm_num) rows225C_61 c53_2 (by norm_num)

theorem c53_0 : rowsJ 53 54 0 400 ≤ 1581041141728990 :=
  rowsJ_le_of_split 53 54 (by norm_num) (by norm_num) rows225C_60 c53_1 (by norm_num)

theorem hr53 : rows 53 54 ≤ 1581041141728990 := rows_le_of_rowsJ 53 54 c53_0

theorem c54_2 : rowsJ 54 55 44 400 ≤ 234111939072032 :=
  rowsJ_le_of_split 54 55 (by norm_num) (by norm_num) rows225C_66 rows225C_67 (by norm_num)

theorem c54_1 : rowsJ 54 55 35 400 ≤ 557031887865860 :=
  rowsJ_le_of_split 54 55 (by norm_num) (by norm_num) rows225C_65 c54_2 (by norm_num)

theorem c54_0 : rowsJ 54 55 0 400 ≤ 1551627165742337 :=
  rowsJ_le_of_split 54 55 (by norm_num) (by norm_num) rows225C_64 c54_1 (by norm_num)

theorem hr54 : rows 54 55 ≤ 1551627165742337 := rows_le_of_rowsJ 54 55 c54_0

theorem c55_3 : rowsJ 55 56 50 400 ≤ 114986904160180 :=
  rowsJ_le_of_split 55 56 (by norm_num) (by norm_num) rows225C_71 rows225C_72 (by norm_num)

theorem c55_2 : rowsJ 55 56 44 400 ≤ 242134884997767 :=
  rowsJ_le_of_split 55 56 (by norm_num) (by norm_num) rows225C_70 c55_3 (by norm_num)

theorem c55_1 : rowsJ 55 56 35 400 ≤ 546448132467251 :=
  rowsJ_le_of_split 55 56 (by norm_num) (by norm_num) rows225C_69 c55_2 (by norm_num)

theorem c55_0 : rowsJ 55 56 0 400 ≤ 1522760097043002 :=
  rowsJ_le_of_split 55 56 (by norm_num) (by norm_num) rows225C_68 c55_1 (by norm_num)

theorem hr55 : rows 55 56 ≤ 1522760097043002 := rows_le_of_rowsJ 55 56 c55_0

theorem c56_3 : rowsJ 56 57 50 400 ≤ 132501763143753 :=
  rowsJ_le_of_split 56 57 (by norm_num) (by norm_num) rows225C_76 rows225C_77 (by norm_num)

theorem c56_2 : rowsJ 56 57 44 400 ≤ 251625850951668 :=
  rowsJ_le_of_split 56 57 (by norm_num) (by norm_num) rows225C_75 c56_3 (by norm_num)

theorem c56_1 : rowsJ 56 57 35 400 ≤ 537847746522369 :=
  rowsJ_le_of_split 56 57 (by norm_num) (by norm_num) rows225C_74 c56_2 (by norm_num)

theorem c56_0 : rowsJ 56 57 0 400 ≤ 1495385425970116 :=
  rowsJ_le_of_split 56 57 (by norm_num) (by norm_num) rows225C_73 c56_1 (by norm_num)

theorem hr56 : rows 56 57 ≤ 1495385425970116 := rows_le_of_rowsJ 56 57 c56_0

theorem c57_3 : rowsJ 57 58 50 400 ≤ 151651882090136 :=
  rowsJ_le_of_split 57 58 (by norm_num) (by norm_num) rows225C_81 rows225C_82 (by norm_num)

theorem c57_2 : rowsJ 57 58 44 400 ≤ 263241570314905 :=
  rowsJ_le_of_split 57 58 (by norm_num) (by norm_num) rows225C_80 c57_3 (by norm_num)

theorem c57_1 : rowsJ 57 58 35 400 ≤ 532018566804658 :=
  rowsJ_le_of_split 57 58 (by norm_num) (by norm_num) rows225C_79 c57_2 (by norm_num)

theorem c57_0 : rowsJ 57 58 0 400 ≤ 1470266755209302 :=
  rowsJ_le_of_split 57 58 (by norm_num) (by norm_num) rows225C_78 c57_1 (by norm_num)

theorem hr57 : rows 57 58 ≤ 1470266755209302 := rows_le_of_rowsJ 57 58 c57_0

theorem c58_3 : rowsJ 58 59 50 400 ≤ 173195371244614 :=
  rowsJ_le_of_split 58 59 (by norm_num) (by norm_num) rows225C_86 rows225C_87 (by norm_num)

theorem c58_2 : rowsJ 58 59 44 400 ≤ 277736768641619 :=
  rowsJ_le_of_split 58 59 (by norm_num) (by norm_num) rows225C_85 c58_3 (by norm_num)

theorem c58_1 : rowsJ 58 59 35 400 ≤ 529575101861336 :=
  rowsJ_le_of_split 58 59 (by norm_num) (by norm_num) rows225C_84 c58_2 (by norm_num)

theorem c58_0 : rowsJ 58 59 0 400 ≤ 1448128491665379 :=
  rowsJ_le_of_split 58 59 (by norm_num) (by norm_num) rows225C_83 c58_1 (by norm_num)

theorem hr58 : rows 58 59 ≤ 1448128491665379 := rows_le_of_rowsJ 58 59 c58_0

theorem c59_4 : rowsJ 59 60 55 400 ≤ 114229485571716 :=
  rowsJ_le_of_split 59 60 (by norm_num) (by norm_num) rows225C_92 rows225C_93 (by norm_num)

theorem c59_3 : rowsJ 59 60 50 400 ≤ 197750133342408 :=
  rowsJ_le_of_split 59 60 (by norm_num) (by norm_num) rows225C_91 c59_4 (by norm_num)

theorem c59_2 : rowsJ 59 60 44 400 ≤ 295734671019597 :=
  rowsJ_le_of_split 59 60 (by norm_num) (by norm_num) rows225C_90 c59_3 (by norm_num)

theorem c59_1 : rowsJ 59 60 35 400 ≤ 531275238675192 :=
  rowsJ_le_of_split 59 60 (by norm_num) (by norm_num) rows225C_89 c59_2 (by norm_num)

theorem c59_0 : rowsJ 59 60 0 400 ≤ 1429616259345460 :=
  rowsJ_le_of_split 59 60 (by norm_num) (by norm_num) rows225C_88 c59_1 (by norm_num)

theorem hr59 : rows 59 60 ≤ 1429616259345460 := rows_le_of_rowsJ 59 60 c59_0

theorem c60_4 : rowsJ 60 61 55 400 ≤ 144251801322512 :=
  rowsJ_le_of_split 60 61 (by norm_num) (by norm_num) rows225C_98 rows225C_99 (by norm_num)

theorem c60_3 : rowsJ 60 61 50 400 ≤ 226123971872051 :=
  rowsJ_le_of_split 60 61 (by norm_num) (by norm_num) rows225C_97 c60_4 (by norm_num)

theorem c60_2 : rowsJ 60 61 44 400 ≤ 318040401962189 :=
  rowsJ_le_of_split 60 61 (by norm_num) (by norm_num) rows225C_96 c60_3 (by norm_num)

theorem c60_1 : rowsJ 60 61 35 400 ≤ 537820342142213 :=
  rowsJ_le_of_split 60 61 (by norm_num) (by norm_num) rows225C_95 c60_2 (by norm_num)

theorem c60_0 : rowsJ 60 61 0 400 ≤ 1415630248778012 :=
  rowsJ_le_of_split 60 61 (by norm_num) (by norm_num) rows225C_94 c60_1 (by norm_num)

theorem hr60 : rows 60 61 ≤ 1415630248778012 := rows_le_of_rowsJ 60 61 c60_0

theorem c61_4 : rowsJ 61 62 55 400 ≤ 178457237711299 :=
  rowsJ_le_of_split 61 62 (by norm_num) (by norm_num) rows225C_104 rows225C_105 (by norm_num)

theorem c61_3 : rowsJ 61 62 50 400 ≤ 259040292917014 :=
  rowsJ_le_of_split 61 62 (by norm_num) (by norm_num) rows225C_103 c61_4 (by norm_num)

theorem c61_2 : rowsJ 61 62 44 400 ≤ 345383797605658 :=
  rowsJ_le_of_split 61 62 (by norm_num) (by norm_num) rows225C_102 c61_3 (by norm_num)

theorem c61_1 : rowsJ 61 62 35 400 ≤ 550040622231935 :=
  rowsJ_le_of_split 61 62 (by norm_num) (by norm_num) rows225C_101 c61_2 (by norm_num)

theorem c61_0 : rowsJ 61 62 0 400 ≤ 1406887163069012 :=
  rowsJ_le_of_split 61 62 (by norm_num) (by norm_num) rows225C_100 c61_1 (by norm_num)

theorem hr61 : rows 61 62 ≤ 1406887163069012 := rows_le_of_rowsJ 61 62 c61_0

theorem c62_4 : rowsJ 62 63 55 400 ≤ 217586923274870 :=
  rowsJ_le_of_split 62 63 (by norm_num) (by norm_num) rows225C_110 rows225C_111 (by norm_num)

theorem c62_3 : rowsJ 62 63 50 400 ≤ 297404750814288 :=
  rowsJ_le_of_split 62 63 (by norm_num) (by norm_num) rows225C_109 c62_4 (by norm_num)

theorem c62_2 : rowsJ 62 63 44 400 ≤ 378668540710301 :=
  rowsJ_le_of_split 62 63 (by norm_num) (by norm_num) rows225C_108 c62_3 (by norm_num)

theorem c62_1 : rowsJ 62 63 35 400 ≤ 568734694493647 :=
  rowsJ_le_of_split 62 63 (by norm_num) (by norm_num) rows225C_107 c62_2 (by norm_num)

theorem c62_0 : rowsJ 62 63 0 400 ≤ 1404297276785078 :=
  rowsJ_le_of_split 62 63 (by norm_num) (by norm_num) rows225C_106 c62_1 (by norm_num)

theorem hr62 : rows 62 63 ≤ 1404297276785078 := rows_le_of_rowsJ 62 63 c62_0

theorem c63_5 : rowsJ 63 64 59 400 ≤ 169307024148203 :=
  rowsJ_le_of_split 63 64 (by norm_num) (by norm_num) rows225C_117 rows225C_118 (by norm_num)

theorem c63_4 : rowsJ 63 64 55 400 ≤ 262106490264769 :=
  rowsJ_le_of_split 63 64 (by norm_num) (by norm_num) rows225C_116 c63_5 (by norm_num)

theorem c63_3 : rowsJ 63 64 50 400 ≤ 341501822080358 :=
  rowsJ_le_of_split 63 64 (by norm_num) (by norm_num) rows225C_115 c63_4 (by norm_num)

theorem c63_2 : rowsJ 63 64 44 400 ≤ 418186677478758 :=
  rowsJ_le_of_split 63 64 (by norm_num) (by norm_num) rows225C_114 c63_3 (by norm_num)

theorem c63_1 : rowsJ 63 64 35 400 ≤ 594337006063682 :=
  rowsJ_le_of_split 63 64 (by norm_num) (by norm_num) rows225C_113 c63_2 (by norm_num)

theorem c63_0 : rowsJ 63 64 0 400 ≤ 1408270011587313 :=
  rowsJ_le_of_split 63 64 (by norm_num) (by norm_num) rows225C_112 c63_1 (by norm_num)

theorem hr63 : rows 63 64 ≤ 1408270011587313 := rows_le_of_rowsJ 63 64 c63_0

theorem c64_5 : rowsJ 64 65 59 400 ≤ 210514469591543 :=
  rowsJ_le_of_split 64 65 (by norm_num) (by norm_num) rows225C_124 rows225C_125 (by norm_num)

theorem c64_4 : rowsJ 64 65 55 400 ≤ 305399514208164 :=
  rowsJ_le_of_split 64 65 (by norm_num) (by norm_num) rows225C_123 c64_5 (by norm_num)

theorem c64_3 : rowsJ 64 65 50 400 ≤ 384908605736737 :=
  rowsJ_le_of_split 64 65 (by norm_num) (by norm_num) rows225C_122 c64_4 (by norm_num)

theorem c64_2 : rowsJ 64 65 44 400 ≤ 457514051225898 :=
  rowsJ_le_of_split 64 65 (by norm_num) (by norm_num) rows225C_121 c64_3 (by norm_num)

theorem c64_1 : rowsJ 64 65 35 400 ≤ 620278396633180 :=
  rowsJ_le_of_split 64 65 (by norm_num) (by norm_num) rows225C_120 c64_2 (by norm_num)

theorem c64_0 : rowsJ 64 65 0 400 ≤ 1412349568626600 :=
  rowsJ_le_of_split 64 65 (by norm_num) (by norm_num) rows225C_119 c64_1 (by norm_num)

theorem hr64 : rows 64 65 ≤ 1412349568626600 := rows_le_of_rowsJ 64 65 c64_0

theorem c65_5 : rowsJ 65 66 59 400 ≤ 250095009384292 :=
  rowsJ_le_of_split 65 66 (by norm_num) (by norm_num) rows225C_131 rows225C_132 (by norm_num)

theorem c65_4 : rowsJ 65 66 55 400 ≤ 347419911084381 :=
  rowsJ_le_of_split 65 66 (by norm_num) (by norm_num) rows225C_130 c65_5 (by norm_num)

theorem c65_3 : rowsJ 65 66 50 400 ≤ 427394613346357 :=
  rowsJ_le_of_split 65 66 (by norm_num) (by norm_num) rows225C_129 c65_4 (by norm_num)

theorem c65_2 : rowsJ 65 66 44 400 ≤ 496428923854757 :=
  rowsJ_le_of_split 65 66 (by norm_num) (by norm_num) rows225C_128 c65_3 (by norm_num)

theorem c65_1 : rowsJ 65 66 35 400 ≤ 646483592239067 :=
  rowsJ_le_of_split 65 66 (by norm_num) (by norm_num) rows225C_127 c65_2 (by norm_num)

theorem c65_0 : rowsJ 65 66 0 400 ≤ 1416343865328257 :=
  rowsJ_le_of_split 65 66 (by norm_num) (by norm_num) rows225C_126 c65_1 (by norm_num)

theorem hr65 : rows 65 66 ≤ 1416343865328257 := rows_le_of_rowsJ 65 66 c65_0

theorem c66_5 : rowsJ 66 67 59 400 ≤ 286250005519058 :=
  rowsJ_le_of_split 66 67 (by norm_num) (by norm_num) rows225C_138 rows225C_139 (by norm_num)

theorem c66_4 : rowsJ 66 67 55 400 ≤ 386380775679453 :=
  rowsJ_le_of_split 66 67 (by norm_num) (by norm_num) rows225C_137 c66_5 (by norm_num)

theorem c66_3 : rowsJ 66 67 50 400 ≤ 467347216909004 :=
  rowsJ_le_of_split 66 67 (by norm_num) (by norm_num) rows225C_136 c66_4 (by norm_num)

theorem c66_2 : rowsJ 66 67 44 400 ≤ 533318143040019 :=
  rowsJ_le_of_split 66 67 (by norm_num) (by norm_num) rows225C_135 c66_3 (by norm_num)

theorem c66_1 : rowsJ 66 67 35 400 ≤ 671231588437817 :=
  rowsJ_le_of_split 66 67 (by norm_num) (by norm_num) rows225C_134 c66_2 (by norm_num)

theorem c66_0 : rowsJ 66 67 0 400 ≤ 1418738959050919 :=
  rowsJ_le_of_split 66 67 (by norm_num) (by norm_num) rows225C_133 c66_1 (by norm_num)

theorem hr66 : rows 66 67 ≤ 1418738959050919 := rows_le_of_rowsJ 66 67 c66_0

theorem c67_6 : rowsJ 67 68 63 400 ≤ 177406249207745 :=
  rowsJ_le_of_split 67 68 (by norm_num) (by norm_num) rows225C_146 rows225C_147 (by norm_num)

theorem c67_5 : rowsJ 67 68 59 400 ≤ 320580640206847 :=
  rowsJ_le_of_split 67 68 (by norm_num) (by norm_num) rows225C_145 c67_6 (by norm_num)

theorem c67_4 : rowsJ 67 68 55 400 ≤ 423885962635712 :=
  rowsJ_le_of_split 67 68 (by norm_num) (by norm_num) rows225C_144 c67_5 (by norm_num)

theorem c67_3 : rowsJ 67 68 50 400 ≤ 506206894831073 :=
  rowsJ_le_of_split 67 68 (by norm_num) (by norm_num) rows225C_143 c67_4 (by norm_num)

theorem c67_2 : rowsJ 67 68 44 400 ≤ 569632168819248 :=
  rowsJ_le_of_split 67 68 (by norm_num) (by norm_num) rows225C_142 c67_3 (by norm_num)

theorem c67_1 : rowsJ 67 68 35 400 ≤ 696084509664832 :=
  rowsJ_le_of_split 67 68 (by norm_num) (by norm_num) rows225C_141 c67_2 (by norm_num)

theorem c67_0 : rowsJ 67 68 0 400 ≤ 1420979116647086 :=
  rowsJ_le_of_split 67 68 (by norm_num) (by norm_num) rows225C_140 c67_1 (by norm_num)

theorem hr67 : rows 67 68 ≤ 1420979116647086 := rows_le_of_rowsJ 67 68 c67_0

theorem c68_6 : rowsJ 68 69 63 400 ≤ 207107218140412 :=
  rowsJ_le_of_split 68 69 (by norm_num) (by norm_num) rows225C_154 rows225C_155 (by norm_num)

theorem c68_5 : rowsJ 68 69 59 400 ≤ 351274538674770 :=
  rowsJ_le_of_split 68 69 (by norm_num) (by norm_num) rows225C_153 c68_6 (by norm_num)

theorem c68_4 : rowsJ 68 69 55 400 ≤ 458136053635924 :=
  rowsJ_le_of_split 68 69 (by norm_num) (by norm_num) rows225C_152 c68_5 (by norm_num)

theorem c68_3 : rowsJ 68 69 50 400 ≤ 542353830396765 :=
  rowsJ_le_of_split 68 69 (by norm_num) (by norm_num) rows225C_151 c68_4 (by norm_num)

theorem c68_2 : rowsJ 68 69 44 400 ≤ 603751414462365 :=
  rowsJ_le_of_split 68 69 (by norm_num) (by norm_num) rows225C_150 c68_3 (by norm_num)

theorem c68_1 : rowsJ 68 69 35 400 ≤ 719313257626087 :=
  rowsJ_le_of_split 68 69 (by norm_num) (by norm_num) rows225C_149 c68_2 (by norm_num)

theorem c68_0 : rowsJ 68 69 0 400 ≤ 1421451646334800 :=
  rowsJ_le_of_split 68 69 (by norm_num) (by norm_num) rows225C_148 c68_1 (by norm_num)

theorem hr68 : rows 68 69 ≤ 1421451646334800 := rows_le_of_rowsJ 68 69 c68_0

theorem c69_6 : rowsJ 69 70 63 400 ≤ 234853854868333 :=
  rowsJ_le_of_split 69 70 (by norm_num) (by norm_num) rows225C_162 rows225C_163 (by norm_num)

theorem c69_5 : rowsJ 69 70 59 400 ≤ 379925671702769 :=
  rowsJ_le_of_split 69 70 (by norm_num) (by norm_num) rows225C_161 c69_6 (by norm_num)

theorem c69_4 : rowsJ 69 70 55 400 ≤ 490728456338020 :=
  rowsJ_le_of_split 69 70 (by norm_num) (by norm_num) rows225C_160 c69_5 (by norm_num)

theorem c69_3 : rowsJ 69 70 50 400 ≤ 577193845083765 :=
  rowsJ_le_of_split 69 70 (by norm_num) (by norm_num) rows225C_159 c69_4 (by norm_num)

theorem c69_2 : rowsJ 69 70 44 400 ≤ 637092975309018 :=
  rowsJ_le_of_split 69 70 (by norm_num) (by norm_num) rows225C_158 c69_3 (by norm_num)

theorem c69_1 : rowsJ 69 70 35 400 ≤ 742490363203434 :=
  rowsJ_le_of_split 69 70 (by norm_num) (by norm_num) rows225C_157 c69_2 (by norm_num)

theorem c69_0 : rowsJ 69 70 0 400 ≤ 1421704219524968 :=
  rowsJ_le_of_split 69 70 (by norm_num) (by norm_num) rows225C_156 c69_1 (by norm_num)

theorem hr69 : rows 69 70 ≤ 1421704219524968 := rows_le_of_rowsJ 69 70 c69_0

theorem c70_6 : rowsJ 70 71 63 400 ≤ 260581717015580 :=
  rowsJ_le_of_split 70 71 (by norm_num) (by norm_num) rows225C_170 rows225C_171 (by norm_num)

theorem c70_5 : rowsJ 70 71 59 400 ≤ 404853266534487 :=
  rowsJ_le_of_split 70 71 (by norm_num) (by norm_num) rows225C_169 c70_6 (by norm_num)

theorem c70_4 : rowsJ 70 71 55 400 ≤ 519849561001495 :=
  rowsJ_le_of_split 70 71 (by norm_num) (by norm_num) rows225C_168 c70_5 (by norm_num)

theorem c70_3 : rowsJ 70 71 50 400 ≤ 609123329189060 :=
  rowsJ_le_of_split 70 71 (by norm_num) (by norm_num) rows225C_167 c70_4 (by norm_num)

theorem c70_2 : rowsJ 70 71 44 400 ≤ 668054256817415 :=
  rowsJ_le_of_split 70 71 (by norm_num) (by norm_num) rows225C_166 c70_3 (by norm_num)

theorem c70_1 : rowsJ 70 71 35 400 ≤ 763862281173031 :=
  rowsJ_le_of_split 70 71 (by norm_num) (by norm_num) rows225C_165 c70_2 (by norm_num)

theorem c70_0 : rowsJ 70 71 0 400 ≤ 1420102181683515 :=
  rowsJ_le_of_split 70 71 (by norm_num) (by norm_num) rows225C_164 c70_1 (by norm_num)

theorem hr70 : rows 70 71 ≤ 1420102181683515 := rows_le_of_rowsJ 70 71 c70_0

theorem c71_6 : rowsJ 71 72 63 400 ≤ 284295759212164 :=
  rowsJ_le_of_split 71 72 (by norm_num) (by norm_num) rows225C_178 rows225C_179 (by norm_num)

theorem c71_5 : rowsJ 71 72 59 400 ≤ 427718486794771 :=
  rowsJ_le_of_split 71 72 (by norm_num) (by norm_num) rows225C_177 c71_6 (by norm_num)

theorem c71_4 : rowsJ 71 72 55 400 ≤ 547090023429996 :=
  rowsJ_le_of_split 71 72 (by norm_num) (by norm_num) rows225C_176 c71_5 (by norm_num)

theorem c71_3 : rowsJ 71 72 50 400 ≤ 639537468899171 :=
  rowsJ_le_of_split 71 72 (by norm_num) (by norm_num) rows225C_175 c71_4 (by norm_num)

theorem c71_2 : rowsJ 71 72 44 400 ≤ 698043083370462 :=
  rowsJ_le_of_split 71 72 (by norm_num) (by norm_num) rows225C_174 c71_3 (by norm_num)

theorem c71_1 : rowsJ 71 72 35 400 ≤ 784996999785321 :=
  rowsJ_le_of_split 71 72 (by norm_num) (by norm_num) rows225C_173 c71_2 (by norm_num)

theorem c71_0 : rowsJ 71 72 0 400 ≤ 1418092511296108 :=
  rowsJ_le_of_split 71 72 (by norm_num) (by norm_num) rows225C_172 c71_1 (by norm_num)

theorem hr71 : rows 71 72 ≤ 1418092511296108 := rows_le_of_rowsJ 71 72 c71_0

theorem c72_6 : rowsJ 72 73 63 400 ≤ 305923379455479 :=
  rowsJ_le_of_split 72 73 (by norm_num) (by norm_num) rows225C_186 rows225C_187 (by norm_num)

theorem c72_5 : rowsJ 72 73 59 400 ≤ 446829832376409 :=
  rowsJ_le_of_split 72 73 (by norm_num) (by norm_num) rows225C_185 c72_6 (by norm_num)

theorem c72_4 : rowsJ 72 73 55 400 ≤ 570620213186552 :=
  rowsJ_le_of_split 72 73 (by norm_num) (by norm_num) rows225C_184 c72_5 (by norm_num)

theorem c72_3 : rowsJ 72 73 50 400 ≤ 666797795716693 :=
  rowsJ_le_of_split 72 73 (by norm_num) (by norm_num) rows225C_183 c72_4 (by norm_num)

theorem c72_2 : rowsJ 72 73 44 400 ≤ 725422826280585 :=
  rowsJ_le_of_split 72 73 (by norm_num) (by norm_num) rows225C_182 c72_3 (by norm_num)

theorem c72_1 : rowsJ 72 73 35 400 ≤ 804144968453004 :=
  rowsJ_le_of_split 72 73 (by norm_num) (by norm_num) rows225C_181 c72_2 (by norm_num)

theorem c72_0 : rowsJ 72 73 0 400 ≤ 1414143695393834 :=
  rowsJ_le_of_split 72 73 (by norm_num) (by norm_num) rows225C_180 c72_1 (by norm_num)

theorem hr72 : rows 72 73 ≤ 1414143695393834 := rows_le_of_rowsJ 72 73 c72_0

theorem c73_6 : rowsJ 73 74 64 400 ≤ 292506038361175 :=
  rowsJ_le_of_split 73 74 (by norm_num) (by norm_num) rows225C_194 rows225C_195 (by norm_num)

theorem c73_5 : rowsJ 73 74 59 400 ≤ 463842554949553 :=
  rowsJ_le_of_split 73 74 (by norm_num) (by norm_num) rows225C_193 c73_6 (by norm_num)

theorem c73_4 : rowsJ 73 74 55 400 ≤ 592023573427528 :=
  rowsJ_le_of_split 73 74 (by norm_num) (by norm_num) rows225C_192 c73_5 (by norm_num)

theorem c73_3 : rowsJ 73 74 50 400 ≤ 692313225415533 :=
  rowsJ_le_of_split 73 74 (by norm_num) (by norm_num) rows225C_191 c73_4 (by norm_num)

theorem c73_2 : rowsJ 73 74 44 400 ≤ 751616488179877 :=
  rowsJ_le_of_split 73 74 (by norm_num) (by norm_num) rows225C_190 c73_3 (by norm_num)

theorem c73_1 : rowsJ 73 74 35 400 ≤ 822854037267431 :=
  rowsJ_le_of_split 73 74 (by norm_num) (by norm_num) rows225C_189 c73_2 (by norm_num)

theorem c73_0 : rowsJ 73 74 0 400 ≤ 1409681718328848 :=
  rowsJ_le_of_split 73 74 (by norm_num) (by norm_num) rows225C_188 c73_1 (by norm_num)

theorem hr73 : rows 73 74 ≤ 1409681718328848 := rows_le_of_rowsJ 73 74 c73_0

theorem c74_6 : rowsJ 74 75 64 400 ≤ 310538271512515 :=
  rowsJ_le_of_split 74 75 (by norm_num) (by norm_num) rows225C_202 rows225C_203 (by norm_num)

theorem c74_5 : rowsJ 74 75 59 400 ≤ 478675108774798 :=
  rowsJ_le_of_split 74 75 (by norm_num) (by norm_num) rows225C_201 c74_6 (by norm_num)

theorem c74_4 : rowsJ 74 75 55 400 ≤ 609600144792957 :=
  rowsJ_le_of_split 74 75 (by norm_num) (by norm_num) rows225C_200 c74_5 (by norm_num)

theorem c74_3 : rowsJ 74 75 50 400 ≤ 714433637529469 :=
  rowsJ_le_of_split 74 75 (by norm_num) (by norm_num) rows225C_199 c74_4 (by norm_num)

theorem c74_2 : rowsJ 74 75 44 400 ≤ 774976661993979 :=
  rowsJ_le_of_split 74 75 (by norm_num) (by norm_num) rows225C_198 c74_3 (by norm_num)

theorem c74_1 : rowsJ 74 75 35 400 ≤ 839361873284672 :=
  rowsJ_le_of_split 74 75 (by norm_num) (by norm_num) rows225C_197 c74_2 (by norm_num)

theorem c74_0 : rowsJ 74 75 0 400 ≤ 1403067588063476 :=
  rowsJ_le_of_split 74 75 (by norm_num) (by norm_num) rows225C_196 c74_1 (by norm_num)

theorem hr74 : rows 74 75 ≤ 1403067588063476 := rows_le_of_rowsJ 74 75 c74_0

theorem c75_6 : rowsJ 75 76 64 400 ≤ 326354830457335 :=
  rowsJ_le_of_split 75 76 (by norm_num) (by norm_num) rows225C_210 rows225C_211 (by norm_num)

theorem c75_5 : rowsJ 75 76 59 400 ≤ 491314738813847 :=
  rowsJ_le_of_split 75 76 (by norm_num) (by norm_num) rows225C_209 c75_6 (by norm_num)

theorem c75_4 : rowsJ 75 76 55 400 ≤ 624925973772878 :=
  rowsJ_le_of_split 75 76 (by norm_num) (by norm_num) rows225C_208 c75_5 (by norm_num)

theorem c75_3 : rowsJ 75 76 50 400 ≤ 734530616546961 :=
  rowsJ_le_of_split 75 76 (by norm_num) (by norm_num) rows225C_207 c75_4 (by norm_num)

theorem c75_2 : rowsJ 75 76 44 400 ≤ 796890565570079 :=
  rowsJ_le_of_split 75 76 (by norm_num) (by norm_num) rows225C_206 c75_3 (by norm_num)

theorem c75_1 : rowsJ 75 76 35 400 ≤ 855226419432048 :=
  rowsJ_le_of_split 75 76 (by norm_num) (by norm_num) rows225C_205 c75_2 (by norm_num)

theorem c75_0 : rowsJ 75 76 0 400 ≤ 1395835546954678 :=
  rowsJ_le_of_split 75 76 (by norm_num) (by norm_num) rows225C_204 c75_1 (by norm_num)

theorem hr75 : rows 75 76 ≤ 1395835546954678 := rows_le_of_rowsJ 75 76 c75_0

theorem c76_6 : rowsJ 76 77 64 400 ≤ 339941431047619 :=
  rowsJ_le_of_split 76 77 (by norm_num) (by norm_num) rows225C_218 rows225C_219 (by norm_num)

theorem c76_5 : rowsJ 76 77 59 400 ≤ 501670065725581 :=
  rowsJ_le_of_split 76 77 (by norm_num) (by norm_num) rows225C_217 c76_6 (by norm_num)

theorem c76_4 : rowsJ 76 77 55 400 ≤ 636286466097640 :=
  rowsJ_le_of_split 76 77 (by norm_num) (by norm_num) rows225C_216 c76_5 (by norm_num)

theorem c76_3 : rowsJ 76 77 50 400 ≤ 750965954851416 :=
  rowsJ_le_of_split 76 77 (by norm_num) (by norm_num) rows225C_215 c76_4 (by norm_num)

theorem c76_2 : rowsJ 76 77 44 400 ≤ 815723637718261 :=
  rowsJ_le_of_split 76 77 (by norm_num) (by norm_num) rows225C_214 c76_3 (by norm_num)

theorem c76_1 : rowsJ 76 77 35 400 ≤ 868655072476128 :=
  rowsJ_le_of_split 76 77 (by norm_num) (by norm_num) rows225C_213 c76_2 (by norm_num)

theorem c76_0 : rowsJ 76 77 0 400 ≤ 1386319693940762 :=
  rowsJ_le_of_split 76 77 (by norm_num) (by norm_num) rows225C_212 c76_1 (by norm_num)

theorem hr76 : rows 76 77 ≤ 1386319693940762 := rows_le_of_rowsJ 76 77 c76_0

theorem c77_6 : rowsJ 77 78 66 400 ≤ 292560348114669 :=
  rowsJ_le_of_split 77 78 (by norm_num) (by norm_num) rows225C_226 rows225C_227 (by norm_num)

theorem c77_5 : rowsJ 77 78 60 400 ≤ 476657304410793 :=
  rowsJ_le_of_split 77 78 (by norm_num) (by norm_num) rows225C_225 c77_6 (by norm_num)

theorem c77_4 : rowsJ 77 78 55 400 ≤ 645249735537769 :=
  rowsJ_le_of_split 77 78 (by norm_num) (by norm_num) rows225C_224 c77_5 (by norm_num)

theorem c77_3 : rowsJ 77 78 50 400 ≤ 765097963783666 :=
  rowsJ_le_of_split 77 78 (by norm_num) (by norm_num) rows225C_223 c77_4 (by norm_num)

theorem c77_2 : rowsJ 77 78 44 400 ≤ 832851482541325 :=
  rowsJ_le_of_split 77 78 (by norm_num) (by norm_num) rows225C_222 c77_3 (by norm_num)

theorem c77_1 : rowsJ 77 78 35 400 ≤ 881199754242070 :=
  rowsJ_le_of_split 77 78 (by norm_num) (by norm_num) rows225C_221 c77_2 (by norm_num)

theorem c77_0 : rowsJ 77 78 0 400 ≤ 1375947086836059 :=
  rowsJ_le_of_split 77 78 (by norm_num) (by norm_num) rows225C_220 c77_1 (by norm_num)

theorem hr77 : rows 77 78 ≤ 1375947086836059 := rows_le_of_rowsJ 77 78 c77_0

theorem c78_6 : rowsJ 78 79 66 400 ≤ 302806685880093 :=
  rowsJ_le_of_split 78 79 (by norm_num) (by norm_num) rows225C_234 rows225C_235 (by norm_num)

theorem c78_5 : rowsJ 78 79 60 400 ≤ 482957155766852 :=
  rowsJ_le_of_split 78 79 (by norm_num) (by norm_num) rows225C_233 c78_6 (by norm_num)

theorem c78_4 : rowsJ 78 79 55 400 ≤ 650084740180467 :=
  rowsJ_le_of_split 78 79 (by norm_num) (by norm_num) rows225C_232 c78_5 (by norm_num)

theorem c78_3 : rowsJ 78 79 50 400 ≤ 775273286291839 :=
  rowsJ_le_of_split 78 79 (by norm_num) (by norm_num) rows225C_231 c78_4 (by norm_num)

theorem c78_2 : rowsJ 78 79 44 400 ≤ 846599601218898 :=
  rowsJ_le_of_split 78 79 (by norm_num) (by norm_num) rows225C_230 c78_3 (by norm_num)

theorem c78_1 : rowsJ 78 79 35 400 ≤ 891067019060979 :=
  rowsJ_le_of_split 78 79 (by norm_num) (by norm_num) rows225C_229 c78_2 (by norm_num)

theorem c78_0 : rowsJ 78 79 0 400 ≤ 1363156365368182 :=
  rowsJ_le_of_split 78 79 (by norm_num) (by norm_num) rows225C_228 c78_1 (by norm_num)

theorem hr78 : rows 78 79 ≤ 1363156365368182 := rows_le_of_rowsJ 78 79 c78_0

theorem c79_6 : rowsJ 79 80 66 400 ≤ 310699149191120 :=
  rowsJ_le_of_split 79 80 (by norm_num) (by norm_num) rows225C_242 rows225C_243 (by norm_num)

theorem c79_5 : rowsJ 79 80 60 400 ≤ 486877138963625 :=
  rowsJ_le_of_split 79 80 (by norm_num) (by norm_num) rows225C_241 c79_6 (by norm_num)

theorem c79_4 : rowsJ 79 80 55 400 ≤ 652521513316429 :=
  rowsJ_le_of_split 79 80 (by norm_num) (by norm_num) rows225C_240 c79_5 (by norm_num)

theorem c79_3 : rowsJ 79 80 50 400 ≤ 783079936450664 :=
  rowsJ_le_of_split 79 80 (by norm_num) (by norm_num) rows225C_239 c79_4 (by norm_num)

theorem c79_2 : rowsJ 79 80 44 400 ≤ 858451950596541 :=
  rowsJ_le_of_split 79 80 (by norm_num) (by norm_num) rows225C_238 c79_3 (by norm_num)

theorem c79_1 : rowsJ 79 80 35 400 ≤ 899881339251161 :=
  rowsJ_le_of_split 79 80 (by norm_num) (by norm_num) rows225C_237 c79_2 (by norm_num)

theorem c79_0 : rowsJ 79 80 0 400 ≤ 1349446503406950 :=
  rowsJ_le_of_split 79 80 (by norm_num) (by norm_num) rows225C_236 c79_1 (by norm_num)

theorem hr79 : rows 79 80 ≤ 1349446503406950 := rows_le_of_rowsJ 79 80 c79_0

theorem c80_6 : rowsJ 80 81 67 400 ≤ 290089221988484 :=
  rowsJ_le_of_split 80 81 (by norm_num) (by norm_num) rows225C_250 rows225C_251 (by norm_num)

theorem c80_5 : rowsJ 80 81 60 400 ≤ 488514894295959 :=
  rowsJ_le_of_split 80 81 (by norm_num) (by norm_num) rows225C_249 c80_6 (by norm_num)

theorem c80_4 : rowsJ 80 81 55 400 ≤ 650946893866670 :=
  rowsJ_le_of_split 80 81 (by norm_num) (by norm_num) rows225C_248 c80_5 (by norm_num)

theorem c80_3 : rowsJ 80 81 50 400 ≤ 786982703856337 :=
  rowsJ_le_of_split 80 81 (by norm_num) (by norm_num) rows225C_247 c80_4 (by norm_num)

theorem c80_2 : rowsJ 80 81 44 400 ≤ 866852300294865 :=
  rowsJ_le_of_split 80 81 (by norm_num) (by norm_num) rows225C_246 c80_3 (by norm_num)

theorem c80_1 : rowsJ 80 81 35 400 ≤ 905965195934320 :=
  rowsJ_le_of_split 80 81 (by norm_num) (by norm_num) rows225C_245 c80_2 (by norm_num)

theorem c80_0 : rowsJ 80 81 0 400 ≤ 1333272761193250 :=
  rowsJ_le_of_split 80 81 (by norm_num) (by norm_num) rows225C_244 c80_1 (by norm_num)

theorem hr80 : rows 80 81 ≤ 1333272761193250 := rows_le_of_rowsJ 80 81 c80_0

theorem c81_6 : rowsJ 81 82 67 400 ≤ 294215659230891 :=
  rowsJ_le_of_split 81 82 (by norm_num) (by norm_num) rows225C_258 rows225C_259 (by norm_num)

theorem c81_5 : rowsJ 81 82 60 400 ≤ 487894212416894 :=
  rowsJ_le_of_split 81 82 (by norm_num) (by norm_num) rows225C_257 c81_6 (by norm_num)

theorem c81_4 : rowsJ 81 82 55 400 ≤ 647132692552468 :=
  rowsJ_le_of_split 81 82 (by norm_num) (by norm_num) rows225C_256 c81_5 (by norm_num)

theorem c81_3 : rowsJ 81 82 50 400 ≤ 788608939451477 :=
  rowsJ_le_of_split 81 82 (by norm_num) (by norm_num) rows225C_255 c81_4 (by norm_num)

theorem c81_2 : rowsJ 81 82 44 400 ≤ 873294121443456 :=
  rowsJ_le_of_split 81 82 (by norm_num) (by norm_num) rows225C_254 c81_3 (by norm_num)

theorem c81_1 : rowsJ 81 82 35 400 ≤ 911000984759756 :=
  rowsJ_le_of_split 81 82 (by norm_num) (by norm_num) rows225C_253 c81_2 (by norm_num)

theorem c81_0 : rowsJ 81 82 0 400 ≤ 1316296121731418 :=
  rowsJ_le_of_split 81 82 (by norm_num) (by norm_num) rows225C_252 c81_1 (by norm_num)

theorem hr81 : rows 81 82 ≤ 1316296121731418 := rows_le_of_rowsJ 81 82 c81_0

theorem c82_5 : rowsJ 82 83 61 400 ≤ 455999302603492 :=
  rowsJ_le_of_split 82 83 (by norm_num) (by norm_num) rows225C_265 rows225C_266 (by norm_num)

theorem c82_4 : rowsJ 82 83 55 400 ≤ 641106958480402 :=
  rowsJ_le_of_split 82 83 (by norm_num) (by norm_num) rows225C_264 c82_5 (by norm_num)

theorem c82_3 : rowsJ 82 83 50 400 ≤ 786426142891080 :=
  rowsJ_le_of_split 82 83 (by norm_num) (by norm_num) rows225C_263 c82_4 (by norm_num)

theorem c82_2 : rowsJ 82 83 44 400 ≤ 876249837493014 :=
  rowsJ_le_of_split 82 83 (by norm_num) (by norm_num) rows225C_262 c82_3 (by norm_num)

theorem c82_1 : rowsJ 82 83 35 400 ≤ 913294864786782 :=
  rowsJ_le_of_split 82 83 (by norm_num) (by norm_num) rows225C_261 c82_2 (by norm_num)

theorem c82_0 : rowsJ 82 83 0 400 ≤ 1296959914667108 :=
  rowsJ_le_of_split 82 83 (by norm_num) (by norm_num) rows225C_260 c82_1 (by norm_num)

theorem hr82 : rows 82 83 ≤ 1296959914667108 := rows_le_of_rowsJ 82 83 c82_0

theorem c83_5 : rowsJ 83 84 61 400 ≤ 451796266204459 :=
  rowsJ_le_of_split 83 84 (by norm_num) (by norm_num) rows225C_272 rows225C_273 (by norm_num)

theorem c83_4 : rowsJ 83 84 55 400 ≤ 632979340900240 :=
  rowsJ_le_of_split 83 84 (by norm_num) (by norm_num) rows225C_271 c83_5 (by norm_num)

theorem c83_3 : rowsJ 83 84 50 400 ≤ 782074170004934 :=
  rowsJ_le_of_split 83 84 (by norm_num) (by norm_num) rows225C_270 c83_4 (by norm_num)

theorem c83_2 : rowsJ 83 84 44 400 ≤ 877220937570027 :=
  rowsJ_le_of_split 83 84 (by norm_num) (by norm_num) rows225C_269 c83_3 (by norm_num)

theorem c83_1 : rowsJ 83 84 35 400 ≤ 914543965814541 :=
  rowsJ_le_of_split 83 84 (by norm_num) (by norm_num) rows225C_268 c83_2 (by norm_num)

theorem c83_0 : rowsJ 83 84 0 400 ≤ 1276832990989232 :=
  rowsJ_le_of_split 83 84 (by norm_num) (by norm_num) rows225C_267 c83_1 (by norm_num)

theorem hr83 : rows 83 84 ≤ 1276832990989232 := rows_le_of_rowsJ 83 84 c83_0

theorem c84_5 : rowsJ 84 85 61 400 ≤ 445576198072132 :=
  rowsJ_le_of_split 84 85 (by norm_num) (by norm_num) rows225C_279 rows225C_280 (by norm_num)

theorem c84_4 : rowsJ 84 85 55 400 ≤ 622806030346270 :=
  rowsJ_le_of_split 84 85 (by norm_num) (by norm_num) rows225C_278 c84_5 (by norm_num)

theorem c84_3 : rowsJ 84 85 50 400 ≤ 774042970516027 :=
  rowsJ_le_of_split 84 85 (by norm_num) (by norm_num) rows225C_277 c84_4 (by norm_num)

theorem c84_2 : rowsJ 84 85 44 400 ≤ 874675680838428 :=
  rowsJ_le_of_split 84 85 (by norm_num) (by norm_num) rows225C_276 c84_3 (by norm_num)

theorem c84_1 : rowsJ 84 85 35 400 ≤ 913047000742221 :=
  rowsJ_le_of_split 84 85 (by norm_num) (by norm_num) rows225C_275 c84_2 (by norm_num)

theorem c84_0 : rowsJ 84 85 0 400 ≤ 1254507434710519 :=
  rowsJ_le_of_split 84 85 (by norm_num) (by norm_num) rows225C_274 c84_1 (by norm_num)

theorem hr84 : rows 84 85 ≤ 1254507434710519 := rows_le_of_rowsJ 84 85 c84_0

theorem c85_5 : rowsJ 85 86 62 400 ≤ 411125678154906 :=
  rowsJ_le_of_split 85 86 (by norm_num) (by norm_num) rows225C_286 rows225C_287 (by norm_num)

theorem c85_4 : rowsJ 85 86 55 400 ≤ 610752907444573 :=
  rowsJ_le_of_split 85 86 (by norm_num) (by norm_num) rows225C_285 c85_5 (by norm_num)

theorem c85_3 : rowsJ 85 86 50 400 ≤ 764030810810035 :=
  rowsJ_le_of_split 85 86 (by norm_num) (by norm_num) rows225C_284 c85_4 (by norm_num)

theorem c85_2 : rowsJ 85 86 44 400 ≤ 870346241938564 :=
  rowsJ_le_of_split 85 86 (by norm_num) (by norm_num) rows225C_283 c85_3 (by norm_num)

theorem c85_1 : rowsJ 85 86 35 400 ≤ 910588087761726 :=
  rowsJ_le_of_split 85 86 (by norm_num) (by norm_num) rows225C_282 c85_2 (by norm_num)

theorem c85_0 : rowsJ 85 86 0 400 ≤ 1231595397208346 :=
  rowsJ_le_of_split 85 86 (by norm_num) (by norm_num) rows225C_281 c85_1 (by norm_num)

theorem hr85 : rows 85 86 ≤ 1231595397208346 := rows_le_of_rowsJ 85 86 c85_0

theorem c86_5 : rowsJ 86 87 63 400 ≤ 377049983003260 :=
  rowsJ_le_of_split 86 87 (by norm_num) (by norm_num) rows225C_293 rows225C_294 (by norm_num)

theorem c86_4 : rowsJ 86 87 56 400 ≤ 566925995711918 :=
  rowsJ_le_of_split 86 87 (by norm_num) (by norm_num) rows225C_292 c86_5 (by norm_num)

theorem c86_3 : rowsJ 86 87 50 400 ≤ 750551613232487 :=
  rowsJ_le_of_split 86 87 (by norm_num) (by norm_num) rows225C_291 c86_4 (by norm_num)

theorem c86_2 : rowsJ 86 87 44 400 ≤ 862725031153070 :=
  rowsJ_le_of_split 86 87 (by norm_num) (by norm_num) rows225C_290 c86_3 (by norm_num)

theorem c86_1 : rowsJ 86 87 35 400 ≤ 905485807833656 :=
  rowsJ_le_of_split 86 87 (by norm_num) (by norm_num) rows225C_289 c86_2 (by norm_num)

theorem c86_0 : rowsJ 86 87 0 400 ≤ 1206605109716432 :=
  rowsJ_le_of_split 86 87 (by norm_num) (by norm_num) rows225C_288 c86_1 (by norm_num)

theorem hr86 : rows 86 87 ≤ 1206605109716432 := rows_le_of_rowsJ 86 87 c86_0

theorem c87_5 : rowsJ 87 88 64 400 ≤ 343541489881996 :=
  rowsJ_le_of_split 87 88 (by norm_num) (by norm_num) rows225C_300 rows225C_301 (by norm_num)

theorem c87_4 : rowsJ 87 88 56 400 ≤ 552109632408087 :=
  rowsJ_le_of_split 87 88 (by norm_num) (by norm_num) rows225C_299 c87_5 (by norm_num)

theorem c87_3 : rowsJ 87 88 50 400 ≤ 735323254903355 :=
  rowsJ_le_of_split 87 88 (by norm_num) (by norm_num) rows225C_298 c87_4 (by norm_num)

theorem c87_2 : rowsJ 87 88 44 400 ≤ 853537861986569 :=
  rowsJ_le_of_split 87 88 (by norm_num) (by norm_num) rows225C_297 c87_3 (by norm_num)

theorem c87_1 : rowsJ 87 88 35 400 ≤ 899519258965623 :=
  rowsJ_le_of_split 87 88 (by norm_num) (by norm_num) rows225C_296 c87_2 (by norm_num)

theorem c87_0 : rowsJ 87 88 0 400 ≤ 1181298444875821 :=
  rowsJ_le_of_split 87 88 (by norm_num) (by norm_num) rows225C_295 c87_1 (by norm_num)

theorem hr87 : rows 87 88 ≤ 1181298444875821 := rows_le_of_rowsJ 87 88 c87_0

theorem c88_5 : rowsJ 88 89 64 400 ≤ 332832041751327 :=
  rowsJ_le_of_split 88 89 (by norm_num) (by norm_num) rows225C_307 rows225C_308 (by norm_num)

theorem c88_4 : rowsJ 88 89 56 400 ≤ 535834363142438 :=
  rowsJ_le_of_split 88 89 (by norm_num) (by norm_num) rows225C_306 c88_5 (by norm_num)

theorem c88_3 : rowsJ 88 89 50 400 ≤ 716871636478315 :=
  rowsJ_le_of_split 88 89 (by norm_num) (by norm_num) rows225C_305 c88_4 (by norm_num)

theorem c88_2 : rowsJ 88 89 44 400 ≤ 841316220532288 :=
  rowsJ_le_of_split 88 89 (by norm_num) (by norm_num) rows225C_304 c88_3 (by norm_num)

theorem c88_1 : rowsJ 88 89 35 400 ≤ 891041323833206 :=
  rowsJ_le_of_split 88 89 (by norm_num) (by norm_num) rows225C_303 c88_2 (by norm_num)

theorem c88_0 : rowsJ 88 89 0 400 ≤ 1154180171462127 :=
  rowsJ_le_of_split 88 89 (by norm_num) (by norm_num) rows225C_302 c88_1 (by norm_num)

theorem hr88 : rows 88 89 ≤ 1154180171462127 := rows_le_of_rowsJ 88 89 c88_0

theorem c89_5 : rowsJ 89 90 65 400 ≤ 299572447717429 :=
  rowsJ_le_of_split 89 90 (by norm_num) (by norm_num) rows225C_314 rows225C_315 (by norm_num)

theorem c89_4 : rowsJ 89 90 56 400 ≤ 518226437827445 :=
  rowsJ_le_of_split 89 90 (by norm_num) (by norm_num) rows225C_313 c89_5 (by norm_num)

theorem c89_3 : rowsJ 89 90 50 400 ≤ 697018203532884 :=
  rowsJ_le_of_split 89 90 (by norm_num) (by norm_num) rows225C_312 c89_4 (by norm_num)

theorem c89_2 : rowsJ 89 90 44 400 ≤ 827813647822774 :=
  rowsJ_le_of_split 89 90 (by norm_num) (by norm_num) rows225C_311 c89_3 (by norm_num)

theorem c89_1 : rowsJ 89 90 35 400 ≤ 881859997098185 :=
  rowsJ_le_of_split 89 90 (by norm_num) (by norm_num) rows225C_310 c89_2 (by norm_num)

theorem c89_0 : rowsJ 89 90 0 400 ≤ 1126927827065569 :=
  rowsJ_le_of_split 89 90 (by norm_num) (by norm_num) rows225C_309 c89_1 (by norm_num)

theorem hr89 : rows 89 90 ≤ 1126927827065569 := rows_le_of_rowsJ 89 90 c89_0

theorem c90_5 : rowsJ 90 91 67 400 ≤ 248528809415924 :=
  rowsJ_le_of_split 90 91 (by norm_num) (by norm_num) rows225C_321 rows225C_322 (by norm_num)

theorem c90_4 : rowsJ 90 91 57 400 ≤ 472911805294385 :=
  rowsJ_le_of_split 90 91 (by norm_num) (by norm_num) rows225C_320 c90_5 (by norm_num)

theorem c90_3 : rowsJ 90 91 50 400 ≤ 674309833931595 :=
  rowsJ_le_of_split 90 91 (by norm_num) (by norm_num) rows225C_319 c90_4 (by norm_num)

theorem c90_2 : rowsJ 90 91 44 400 ≤ 811554155132418 :=
  rowsJ_le_of_split 90 91 (by norm_num) (by norm_num) rows225C_318 c90_3 (by norm_num)

theorem c90_1 : rowsJ 90 91 35 400 ≤ 870315393752889 :=
  rowsJ_le_of_split 90 91 (by norm_num) (by norm_num) rows225C_317 c90_2 (by norm_num)

theorem c90_0 : rowsJ 90 91 0 400 ≤ 1098199885674217 :=
  rowsJ_le_of_split 90 91 (by norm_num) (by norm_num) rows225C_316 c90_1 (by norm_num)

theorem hr90 : rows 90 91 ≤ 1098199885674217 := rows_le_of_rowsJ 90 91 c90_0

theorem c91_6 : rowsJ 91 92 86 400 ≤ 25117166537102 :=
  rowsJ_le_of_split 91 92 (by norm_num) (by norm_num) rows225C_329 rows225C_330 (by norm_num)

theorem c91_5 : rowsJ 91 92 68 400 ≤ 219409139895338 :=
  rowsJ_le_of_split 91 92 (by norm_num) (by norm_num) rows225C_328 c91_6 (by norm_num)

theorem c91_4 : rowsJ 91 92 57 400 ≤ 453937626514639 :=
  rowsJ_le_of_split 91 92 (by norm_num) (by norm_num) rows225C_327 c91_5 (by norm_num)

theorem c91_3 : rowsJ 91 92 50 400 ≤ 650605433886538 :=
  rowsJ_le_of_split 91 92 (by norm_num) (by norm_num) rows225C_326 c91_4 (by norm_num)

theorem c91_2 : rowsJ 91 92 44 400 ≤ 794354754418233 :=
  rowsJ_le_of_split 91 92 (by norm_num) (by norm_num) rows225C_325 c91_3 (by norm_num)

theorem c91_1 : rowsJ 91 92 35 400 ≤ 858279968706642 :=
  rowsJ_le_of_split 91 92 (by norm_num) (by norm_num) rows225C_324 c91_2 (by norm_num)

theorem c91_0 : rowsJ 91 92 0 400 ≤ 1069693301581092 :=
  rowsJ_le_of_split 91 92 (by norm_num) (by norm_num) rows225C_323 c91_1 (by norm_num)

theorem hr91 : rows 91 92 ≤ 1069693301581092 := rows_le_of_rowsJ 91 92 c91_0

theorem c92_6 : rowsJ 92 93 86 400 ≤ 25235345605860 :=
  rowsJ_le_of_split 92 93 (by norm_num) (by norm_num) rows225C_337 rows225C_338 (by norm_num)

theorem c92_5 : rowsJ 92 93 69 400 ≤ 191839805500269 :=
  rowsJ_le_of_split 92 93 (by norm_num) (by norm_num) rows225C_336 c92_6 (by norm_num)

theorem c92_4 : rowsJ 92 93 57 400 ≤ 434219125889698 :=
  rowsJ_le_of_split 92 93 (by norm_num) (by norm_num) rows225C_335 c92_5 (by norm_num)

theorem c92_3 : rowsJ 92 93 50 400 ≤ 626153071123633 :=
  rowsJ_le_of_split 92 93 (by norm_num) (by norm_num) rows225C_334 c92_4 (by norm_num)

theorem c92_2 : rowsJ 92 93 44 400 ≤ 774766961143977 :=
  rowsJ_le_of_split 92 93 (by norm_num) (by norm_num) rows225C_333 c92_3 (by norm_num)

theorem c92_1 : rowsJ 92 93 35 400 ≤ 844115497433086 :=
  rowsJ_le_of_split 92 93 (by norm_num) (by norm_num) rows225C_332 c92_2 (by norm_num)

theorem c92_0 : rowsJ 92 93 0 400 ≤ 1039978891279121 :=
  rowsJ_le_of_split 92 93 (by norm_num) (by norm_num) rows225C_331 c92_1 (by norm_num)

theorem hr92 : rows 92 93 ≤ 1039978891279121 := rows_le_of_rowsJ 92 93 c92_0

theorem c93_6 : rowsJ 93 94 87 400 ≤ 20721353703756 :=
  rowsJ_le_of_split 93 94 (by norm_num) (by norm_num) rows225C_345 rows225C_346 (by norm_num)

theorem c93_5 : rowsJ 93 94 75 400 ≤ 104118717925809 :=
  rowsJ_le_of_split 93 94 (by norm_num) (by norm_num) rows225C_344 c93_6 (by norm_num)

theorem c93_4 : rowsJ 93 94 59 400 ≤ 367366185614590 :=
  rowsJ_le_of_split 93 94 (by norm_num) (by norm_num) rows225C_343 c93_5 (by norm_num)

theorem c93_3 : rowsJ 93 94 51 400 ≤ 572198417929916 :=
  rowsJ_le_of_split 93 94 (by norm_num) (by norm_num) rows225C_342 c93_4 (by norm_num)

theorem c93_2 : rowsJ 93 94 44 400 ≤ 754630849126104 :=
  rowsJ_le_of_split 93 94 (by norm_num) (by norm_num) rows225C_341 c93_3 (by norm_num)

theorem c93_1 : rowsJ 93 94 35 400 ≤ 829718295673302 :=
  rowsJ_le_of_split 93 94 (by norm_num) (by norm_num) rows225C_340 c93_2 (by norm_num)

theorem c93_0 : rowsJ 93 94 0 400 ≤ 1010942069308766 :=
  rowsJ_le_of_split 93 94 (by norm_num) (by norm_num) rows225C_339 c93_1 (by norm_num)

theorem hr93 : rows 93 94 ≤ 1010942069308766 := rows_le_of_rowsJ 93 94 c93_0

theorem c94_6 : rowsJ 94 95 88 400 ≤ 17125373379338 :=
  rowsJ_le_of_split 94 95 (by norm_num) (by norm_num) rows225C_353 rows225C_354 (by norm_num)

theorem c94_5 : rowsJ 94 95 80 400 ≤ 54735926742378 :=
  rowsJ_le_of_split 94 95 (by norm_num) (by norm_num) rows225C_352 c94_6 (by norm_num)

theorem c94_4 : rowsJ 94 95 60 400 ≤ 326970521821874 :=
  rowsJ_le_of_split 94 95 (by norm_num) (by norm_num) rows225C_351 c94_5 (by norm_num)

theorem c94_3 : rowsJ 94 95 51 400 ≤ 547608547809659 :=
  rowsJ_le_of_split 94 95 (by norm_num) (by norm_num) rows225C_350 c94_4 (by norm_num)

theorem c94_2 : rowsJ 94 95 44 400 ≤ 732570292888366 :=
  rowsJ_le_of_split 94 95 (by norm_num) (by norm_num) rows225C_349 c94_3 (by norm_num)

theorem c94_1 : rowsJ 94 95 35 400 ≤ 813671343112211 :=
  rowsJ_le_of_split 94 95 (by norm_num) (by norm_num) rows225C_348 c94_2 (by norm_num)

theorem c94_0 : rowsJ 94 95 0 400 ≤ 981181658591162 :=
  rowsJ_le_of_split 94 95 (by norm_num) (by norm_num) rows225C_347 c94_1 (by norm_num)

theorem hr94 : rows 94 95 ≤ 981181658591162 := rows_le_of_rowsJ 94 95 c94_0

theorem c95_7 : rowsJ 95 96 92 400 ≤ 8598836377321 :=
  rowsJ_le_of_split 95 96 (by norm_num) (by norm_num) rows225C_362 rows225C_363 (by norm_num)

theorem c95_6 : rowsJ 95 96 88 400 ≤ 17238222096490 :=
  rowsJ_le_of_split 95 96 (by norm_num) (by norm_num) rows225C_361 c95_7 (by norm_num)

theorem c95_5 : rowsJ 95 96 81 400 ≤ 44749179256645 :=
  rowsJ_le_of_split 95 96 (by norm_num) (by norm_num) rows225C_360 c95_6 (by norm_num)

theorem c95_4 : rowsJ 95 96 60 400 ≤ 309157143899936 :=
  rowsJ_le_of_split 95 96 (by norm_num) (by norm_num) rows225C_359 c95_5 (by norm_num)

theorem c95_3 : rowsJ 95 96 51 400 ≤ 523375172763087 :=
  rowsJ_le_of_split 95 96 (by norm_num) (by norm_num) rows225C_358 c95_4 (by norm_num)

theorem c95_2 : rowsJ 95 96 44 400 ≤ 710782069596566 :=
  rowsJ_le_of_split 95 96 (by norm_num) (by norm_num) rows225C_357 c95_3 (by norm_num)

theorem c95_1 : rowsJ 95 96 35 400 ≤ 798229428006865 :=
  rowsJ_le_of_split 95 96 (by norm_num) (by norm_num) rows225C_356 c95_2 (by norm_num)

theorem c95_0 : rowsJ 95 96 0 400 ≤ 952820009895471 :=
  rowsJ_le_of_split 95 96 (by norm_num) (by norm_num) rows225C_355 c95_1 (by norm_num)

theorem hr95 : rows 95 96 ≤ 952820009895471 := rows_le_of_rowsJ 95 96 c95_0

theorem c96_7 : rowsJ 96 97 92 400 ≤ 10915121623642 :=
  rowsJ_le_of_split 96 97 (by norm_num) (by norm_num) rows225C_371 rows225C_372 (by norm_num)

theorem c96_6 : rowsJ 96 97 88 400 ≤ 18098334137944 :=
  rowsJ_le_of_split 96 97 (by norm_num) (by norm_num) rows225C_370 c96_7 (by norm_num)

theorem c96_5 : rowsJ 96 97 82 400 ≤ 37312912676499 :=
  rowsJ_le_of_split 96 97 (by norm_num) (by norm_num) rows225C_369 c96_6 (by norm_num)

theorem c96_4 : rowsJ 96 97 61 400 ≤ 273266121796892 :=
  rowsJ_le_of_split 96 97 (by norm_num) (by norm_num) rows225C_368 c96_5 (by norm_num)

theorem c96_3 : rowsJ 96 97 51 400 ≤ 500094833517233 :=
  rowsJ_le_of_split 96 97 (by norm_num) (by norm_num) rows225C_367 c96_4 (by norm_num)

theorem c96_2 : rowsJ 96 97 44 400 ≤ 688256524570658 :=
  rowsJ_le_of_split 96 97 (by norm_num) (by norm_num) rows225C_366 c96_3 (by norm_num)

theorem c96_1 : rowsJ 96 97 35 400 ≤ 782313359413972 :=
  rowsJ_le_of_split 96 97 (by norm_num) (by norm_num) rows225C_365 c96_2 (by norm_num)

theorem c96_0 : rowsJ 96 97 0 400 ≤ 924965248893583 :=
  rowsJ_le_of_split 96 97 (by norm_num) (by norm_num) rows225C_364 c96_1 (by norm_num)

theorem hr96 : rows 96 97 ≤ 924965248893583 := rows_le_of_rowsJ 96 97 c96_0

theorem c97_8 : rowsJ 97 98 94 400 ≤ 9589367422349 :=
  rowsJ_le_of_split 97 98 (by norm_num) (by norm_num) rows225C_381 rows225C_382 (by norm_num)

theorem c97_7 : rowsJ 97 98 91 400 ≤ 14145392874691 :=
  rowsJ_le_of_split 97 98 (by norm_num) (by norm_num) rows225C_380 c97_8 (by norm_num)

theorem c97_6 : rowsJ 97 98 88 400 ≤ 18624038290552 :=
  rowsJ_le_of_split 97 98 (by norm_num) (by norm_num) rows225C_379 c97_7 (by norm_num)

theorem c97_5 : rowsJ 97 98 82 400 ≤ 35088420827529 :=
  rowsJ_le_of_split 97 98 (by norm_num) (by norm_num) rows225C_378 c97_6 (by norm_num)

theorem c97_4 : rowsJ 97 98 62 400 ≤ 239698873540119 :=
  rowsJ_le_of_split 97 98 (by norm_num) (by norm_num) rows225C_377 c97_5 (by norm_num)

theorem c97_3 : rowsJ 97 98 51 400 ≤ 476802478270354 :=
  rowsJ_le_of_split 97 98 (by norm_num) (by norm_num) rows225C_376 c97_4 (by norm_num)

theorem c97_2 : rowsJ 97 98 44 400 ≤ 665595489145921 :=
  rowsJ_le_of_split 97 98 (by norm_num) (by norm_num) rows225C_375 c97_3 (by norm_num)

theorem c97_1 : rowsJ 97 98 35 400 ≤ 766613155921930 :=
  rowsJ_le_of_split 97 98 (by norm_num) (by norm_num) rows225C_374 c97_2 (by norm_num)

theorem c97_0 : rowsJ 97 98 0 400 ≤ 898127017060677 :=
  rowsJ_le_of_split 97 98 (by norm_num) (by norm_num) rows225C_373 c97_1 (by norm_num)

theorem hr97 : rows 97 98 ≤ 898127017060677 := rows_le_of_rowsJ 97 98 c97_0

theorem c98_8 : rowsJ 98 99 95 400 ≤ 9045224571142 :=
  rowsJ_le_of_split 98 99 (by norm_num) (by norm_num) rows225C_391 rows225C_392 (by norm_num)

theorem c98_7 : rowsJ 98 99 92 400 ≤ 14171969912550 :=
  rowsJ_le_of_split 98 99 (by norm_num) (by norm_num) rows225C_390 c98_8 (by norm_num)

theorem c98_6 : rowsJ 98 99 89 400 ≤ 17607221929755 :=
  rowsJ_le_of_split 98 99 (by norm_num) (by norm_num) rows225C_389 c98_7 (by norm_num)

theorem c98_5 : rowsJ 98 99 84 400 ≤ 26570397422449 :=
  rowsJ_le_of_split 98 99 (by norm_num) (by norm_num) rows225C_388 c98_6 (by norm_num)

theorem c98_4 : rowsJ 98 99 65 400 ≤ 178503625581500 :=
  rowsJ_le_of_split 98 99 (by norm_num) (by norm_num) rows225C_387 c98_5 (by norm_num)

theorem c98_3 : rowsJ 98 99 52 400 ≤ 428784570746370 :=
  rowsJ_le_of_split 98 99 (by norm_num) (by norm_num) rows225C_386 c98_4 (by norm_num)

theorem c98_2 : rowsJ 98 99 44 400 ≤ 641214405809406 :=
  rowsJ_le_of_split 98 99 (by norm_num) (by norm_num) rows225C_385 c98_3 (by norm_num)

theorem c98_1 : rowsJ 98 99 35 400 ≤ 749474121344202 :=
  rowsJ_le_of_split 98 99 (by norm_num) (by norm_num) rows225C_384 c98_2 (by norm_num)

theorem c98_0 : rowsJ 98 99 0 400 ≤ 870714872399897 :=
  rowsJ_le_of_split 98 99 (by norm_num) (by norm_num) rows225C_383 c98_1 (by norm_num)

theorem hr98 : rows 98 99 ≤ 870714872399897 := rows_le_of_rowsJ 98 99 c98_0

theorem c99_9 : rowsJ 99 100 96 400 ≤ 7575362294734 :=
  rowsJ_le_of_split 99 100 (by norm_num) (by norm_num) rows225C_402 rows225C_403 (by norm_num)

theorem c99_8 : rowsJ 99 100 94 400 ≤ 11780562764147 :=
  rowsJ_le_of_split 99 100 (by norm_num) (by norm_num) rows225C_401 c99_9 (by norm_num)

theorem c99_7 : rowsJ 99 100 91 400 ≤ 15923942068249 :=
  rowsJ_le_of_split 99 100 (by norm_num) (by norm_num) rows225C_400 c99_8 (by norm_num)

theorem c99_6 : rowsJ 99 100 88 400 ≤ 18683273603972 :=
  rowsJ_le_of_split 99 100 (by norm_num) (by norm_num) rows225C_399 c99_7 (by norm_num)

theorem c99_5 : rowsJ 99 100 84 400 ≤ 24802680705600 :=
  rowsJ_le_of_split 99 100 (by norm_num) (by norm_num) rows225C_398 c99_6 (by norm_num)

theorem c99_4 : rowsJ 99 100 66 400 ≤ 152264590532740 :=
  rowsJ_le_of_split 99 100 (by norm_num) (by norm_num) rows225C_397 c99_5 (by norm_num)

theorem c99_3 : rowsJ 99 100 52 400 ≤ 406100931791638 :=
  rowsJ_le_of_split 99 100 (by norm_num) (by norm_num) rows225C_396 c99_4 (by norm_num)

theorem c99_2 : rowsJ 99 100 44 400 ≤ 616560256932608 :=
  rowsJ_le_of_split 99 100 (by norm_num) (by norm_num) rows225C_395 c99_3 (by norm_num)

theorem c99_1 : rowsJ 99 100 35 400 ≤ 732404890797107 :=
  rowsJ_le_of_split 99 100 (by norm_num) (by norm_num) rows225C_394 c99_2 (by norm_num)

theorem c99_0 : rowsJ 99 100 0 400 ≤ 844231146658324 :=
  rowsJ_le_of_split 99 100 (by norm_num) (by norm_num) rows225C_393 c99_1 (by norm_num)

theorem hr99 : rows 99 100 ≤ 844231146658324 := rows_le_of_rowsJ 99 100 c99_0

theorem c100_10 : rowsJ 100 101 98 400 ≤ 4525976257098 :=
  rowsJ_le_of_split 100 101 (by norm_num) (by norm_num) rows225C_414 rows225C_415 (by norm_num)

theorem c100_9 : rowsJ 100 101 96 400 ≤ 8042945853760 :=
  rowsJ_le_of_split 100 101 (by norm_num) (by norm_num) rows225C_413 c100_10 (by norm_num)

theorem c100_8 : rowsJ 100 101 94 400 ≤ 11982149587020 :=
  rowsJ_le_of_split 100 101 (by norm_num) (by norm_num) rows225C_412 c100_9 (by norm_num)

theorem c100_7 : rowsJ 100 101 91 400 ≤ 16098082716698 :=
  rowsJ_le_of_split 100 101 (by norm_num) (by norm_num) rows225C_411 c100_8 (by norm_num)

theorem c100_6 : rowsJ 100 101 88 400 ≤ 18319607849344 :=
  rowsJ_le_of_split 100 101 (by norm_num) (by norm_num) rows225C_410 c100_7 (by norm_num)

theorem c100_5 : rowsJ 100 101 84 400 ≤ 22998289356931 :=
  rowsJ_le_of_split 100 101 (by norm_num) (by norm_num) rows225C_409 c100_6 (by norm_num)

theorem c100_4 : rowsJ 100 101 68 400 ≤ 117254249888205 :=
  rowsJ_le_of_split 100 101 (by norm_num) (by norm_num) rows225C_408 c100_5 (by norm_num)

theorem c100_3 : rowsJ 100 101 52 400 ≤ 383662576346680 :=
  rowsJ_le_of_split 100 101 (by norm_num) (by norm_num) rows225C_407 c100_4 (by norm_num)

theorem c100_2 : rowsJ 100 101 44 400 ≤ 590305398618446 :=
  rowsJ_le_of_split 100 101 (by norm_num) (by norm_num) rows225C_406 c100_3 (by norm_num)

theorem c100_1 : rowsJ 100 101 35 400 ≤ 714035915934633 :=
  rowsJ_le_of_split 100 101 (by norm_num) (by norm_num) rows225C_405 c100_2 (by norm_num)

theorem c100_0 : rowsJ 100 101 0 400 ≤ 817324367464315 :=
  rowsJ_le_of_split 100 101 (by norm_num) (by norm_num) rows225C_404 c100_1 (by norm_num)

theorem hr100 : rows 100 101 ≤ 817324367464315 := rows_le_of_rowsJ 100 101 c100_0

theorem c101_10 : rowsJ 101 102 98 400 ≤ 5019934892531 :=
  rowsJ_le_of_split 101 102 (by norm_num) (by norm_num) rows225C_426 rows225C_427 (by norm_num)

theorem c101_9 : rowsJ 101 102 96 400 ≤ 8084893958953 :=
  rowsJ_le_of_split 101 102 (by norm_num) (by norm_num) rows225C_425 c101_10 (by norm_num)

theorem c101_8 : rowsJ 101 102 94 400 ≤ 11546370076520 :=
  rowsJ_le_of_split 101 102 (by norm_num) (by norm_num) rows225C_424 c101_9 (by norm_num)

theorem c101_7 : rowsJ 101 102 91 400 ≤ 15635285254614 :=
  rowsJ_le_of_split 101 102 (by norm_num) (by norm_num) rows225C_423 c101_8 (by norm_num)

theorem c101_6 : rowsJ 101 102 88 400 ≤ 17577682188627 :=
  rowsJ_le_of_split 101 102 (by norm_num) (by norm_num) rows225C_422 c101_7 (by norm_num)

theorem c101_5 : rowsJ 101 102 84 400 ≤ 20934544387649 :=
  rowsJ_le_of_split 101 102 (by norm_num) (by norm_num) rows225C_421 c101_6 (by norm_num)

theorem c101_4 : rowsJ 101 102 75 400 ≤ 51597026677717 :=
  rowsJ_le_of_split 101 102 (by norm_num) (by norm_num) rows225C_420 c101_5 (by norm_num)

theorem c101_3 : rowsJ 101 102 53 400 ≤ 339515482953076 :=
  rowsJ_le_of_split 101 102 (by norm_num) (by norm_num) rows225C_419 c101_4 (by norm_num)

theorem c101_2 : rowsJ 101 102 44 400 ≤ 564004802608828 :=
  rowsJ_le_of_split 101 102 (by norm_num) (by norm_num) rows225C_418 c101_3 (by norm_num)

theorem c101_1 : rowsJ 101 102 35 400 ≤ 695906808311005 :=
  rowsJ_le_of_split 101 102 (by norm_num) (by norm_num) rows225C_417 c101_2 (by norm_num)

theorem c101_0 : rowsJ 101 102 0 400 ≤ 791397224727889 :=
  rowsJ_le_of_split 101 102 (by norm_num) (by norm_num) rows225C_416 c101_1 (by norm_num)

theorem hr101 : rows 101 102 ≤ 791397224727889 := rows_le_of_rowsJ 101 102 c101_0

theorem c102_11 : rowsJ 102 103 99 400 ≤ 3932189586603 :=
  rowsJ_le_of_split 102 103 (by norm_num) (by norm_num) rows225C_439 rows225C_440 (by norm_num)

theorem c102_10 : rowsJ 102 103 97 400 ≤ 6399307865318 :=
  rowsJ_le_of_split 102 103 (by norm_num) (by norm_num) rows225C_438 c102_11 (by norm_num)

theorem c102_9 : rowsJ 102 103 95 400 ≤ 9227748267478 :=
  rowsJ_le_of_split 102 103 (by norm_num) (by norm_num) rows225C_437 c102_10 (by norm_num)

theorem c102_8 : rowsJ 102 103 93 400 ≤ 12437290701130 :=
  rowsJ_le_of_split 102 103 (by norm_num) (by norm_num) rows225C_436 c102_9 (by norm_num)

theorem c102_7 : rowsJ 102 103 91 400 ≤ 14844350695384 :=
  rowsJ_le_of_split 102 103 (by norm_num) (by norm_num) rows225C_435 c102_8 (by norm_num)

theorem c102_6 : rowsJ 102 103 88 400 ≤ 16684279035706 :=
  rowsJ_le_of_split 102 103 (by norm_num) (by norm_num) rows225C_434 c102_7 (by norm_num)

theorem c102_5 : rowsJ 102 103 84 400 ≤ 18939413174396 :=
  rowsJ_le_of_split 102 103 (by norm_num) (by norm_num) rows225C_433 c102_6 (by norm_num)

theorem c102_4 : rowsJ 102 103 77 400 ≤ 36134857792250 :=
  rowsJ_le_of_split 102 103 (by norm_num) (by norm_num) rows225C_432 c102_5 (by norm_num)

theorem c102_3 : rowsJ 102 103 53 400 ≤ 318279755826937 :=
  rowsJ_le_of_split 102 103 (by norm_num) (by norm_num) rows225C_431 c102_4 (by norm_num)

theorem c102_2 : rowsJ 102 103 44 400 ≤ 536295832323400 :=
  rowsJ_le_of_split 102 103 (by norm_num) (by norm_num) rows225C_430 c102_3 (by norm_num)

theorem c102_1 : rowsJ 102 103 35 400 ≤ 676581518402450 :=
  rowsJ_le_of_split 102 103 (by norm_num) (by norm_num) rows225C_429 c102_2 (by norm_num)

theorem c102_0 : rowsJ 102 103 0 400 ≤ 765214686797473 :=
  rowsJ_le_of_split 102 103 (by norm_num) (by norm_num) rows225C_428 c102_1 (by norm_num)

theorem hr102 : rows 102 103 ≤ 765214686797473 := rows_le_of_rowsJ 102 103 c102_0

theorem c103_11 : rowsJ 103 104 100 400 ≤ 2970663759983 :=
  rowsJ_le_of_split 103 104 (by norm_num) (by norm_num) rows225C_452 rows225C_453 (by norm_num)

theorem c103_10 : rowsJ 103 104 97 400 ≤ 5991318381120 :=
  rowsJ_le_of_split 103 104 (by norm_num) (by norm_num) rows225C_451 c103_11 (by norm_num)

theorem c103_9 : rowsJ 103 104 95 400 ≤ 8419078577929 :=
  rowsJ_le_of_split 103 104 (by norm_num) (by norm_num) rows225C_450 c103_10 (by norm_num)

theorem c103_8 : rowsJ 103 104 93 400 ≤ 11203006364096 :=
  rowsJ_le_of_split 103 104 (by norm_num) (by norm_num) rows225C_449 c103_9 (by norm_num)

theorem c103_7 : rowsJ 103 104 91 400 ≤ 13593766568812 :=
  rowsJ_le_of_split 103 104 (by norm_num) (by norm_num) rows225C_448 c103_8 (by norm_num)

theorem c103_6 : rowsJ 103 104 88 400 ≤ 15421582529918 :=
  rowsJ_le_of_split 103 104 (by norm_num) (by norm_num) rows225C_447 c103_7 (by norm_num)

theorem c103_5 : rowsJ 103 104 84 400 ≤ 16807623009536 :=
  rowsJ_le_of_split 103 104 (by norm_num) (by norm_num) rows225C_446 c103_6 (by norm_num)

theorem c103_4 : rowsJ 103 104 78 400 ≤ 27707640682537 :=
  rowsJ_le_of_split 103 104 (by norm_num) (by norm_num) rows225C_445 c103_5 (by norm_num)

theorem c103_3 : rowsJ 103 104 54 400 ≤ 277905969524040 :=
  rowsJ_le_of_split 103 104 (by norm_num) (by norm_num) rows225C_444 c103_4 (by norm_num)

theorem c103_2 : rowsJ 103 104 44 400 ≤ 508766413855826 :=
  rowsJ_le_of_split 103 104 (by norm_num) (by norm_num) rows225C_443 c103_3 (by norm_num)

theorem c103_1 : rowsJ 103 104 35 400 ≤ 657661809889827 :=
  rowsJ_le_of_split 103 104 (by norm_num) (by norm_num) rows225C_442 c103_2 (by norm_num)

theorem c103_0 : rowsJ 103 104 0 400 ≤ 740191088864858 :=
  rowsJ_le_of_split 103 104 (by norm_num) (by norm_num) rows225C_441 c103_1 (by norm_num)

theorem hr103 : rows 103 104 ≤ 740191088864858 := rows_le_of_rowsJ 103 104 c103_0

theorem c104_11 : rowsJ 104 105 100 400 ≤ 2833224451435 :=
  rowsJ_le_of_split 104 105 (by norm_num) (by norm_num) rows225C_465 rows225C_466 (by norm_num)

theorem c104_10 : rowsJ 104 105 97 400 ≤ 5348534258303 :=
  rowsJ_le_of_split 104 105 (by norm_num) (by norm_num) rows225C_464 c104_11 (by norm_num)

theorem c104_9 : rowsJ 104 105 95 400 ≤ 7407555912637 :=
  rowsJ_le_of_split 104 105 (by norm_num) (by norm_num) rows225C_463 c104_10 (by norm_num)

theorem c104_8 : rowsJ 104 105 93 400 ≤ 9797179155256 :=
  rowsJ_le_of_split 104 105 (by norm_num) (by norm_num) rows225C_462 c104_9 (by norm_num)

theorem c104_7 : rowsJ 104 105 91 400 ≤ 12171911432463 :=
  rowsJ_le_of_split 104 105 (by norm_num) (by norm_num) rows225C_461 c104_8 (by norm_num)

theorem c104_6 : rowsJ 104 105 88 400 ≤ 13987797027252 :=
  rowsJ_le_of_split 104 105 (by norm_num) (by norm_num) rows225C_460 c104_7 (by norm_num)

theorem c104_5 : rowsJ 104 105 85 400 ≤ 14561523717633 :=
  rowsJ_le_of_split 104 105 (by norm_num) (by norm_num) rows225C_459 c104_6 (by norm_num)

theorem c104_4 : rowsJ 104 105 79 400 ≤ 20999039257469 :=
  rowsJ_le_of_split 104 105 (by norm_num) (by norm_num) rows225C_458 c104_5 (by norm_num)

theorem c104_3 : rowsJ 104 105 55 400 ≤ 240424581337427 :=
  rowsJ_le_of_split 104 105 (by norm_num) (by norm_num) rows225C_457 c104_4 (by norm_num)

theorem c104_2 : rowsJ 104 105 44 400 ≤ 481754593252128 :=
  rowsJ_le_of_split 104 105 (by norm_num) (by norm_num) rows225C_456 c104_3 (by norm_num)

theorem c104_1 : rowsJ 104 105 35 400 ≤ 637678378679471 :=
  rowsJ_le_of_split 104 105 (by norm_num) (by norm_num) rows225C_455 c104_2 (by norm_num)

theorem c104_0 : rowsJ 104 105 0 400 ≤ 714925855498506 :=
  rowsJ_le_of_split 104 105 (by norm_num) (by norm_num) rows225C_454 c104_1 (by norm_num)

theorem hr104 : rows 104 105 ≤ 714925855498506 := rows_le_of_rowsJ 104 105 c104_0

theorem c105_11 : rowsJ 105 106 101 400 ≤ 2026066653786 :=
  rowsJ_le_of_split 105 106 (by norm_num) (by norm_num) rows225C_478 rows225C_479 (by norm_num)

theorem c105_10 : rowsJ 105 106 98 400 ≤ 3883244189225 :=
  rowsJ_le_of_split 105 106 (by norm_num) (by norm_num) rows225C_477 c105_11 (by norm_num)

theorem c105_9 : rowsJ 105 106 95 400 ≤ 6359042044588 :=
  rowsJ_le_of_split 105 106 (by norm_num) (by norm_num) rows225C_476 c105_10 (by norm_num)

theorem c105_8 : rowsJ 105 106 93 400 ≤ 8385260432968 :=
  rowsJ_le_of_split 105 106 (by norm_num) (by norm_num) rows225C_475 c105_9 (by norm_num)

theorem c105_7 : rowsJ 105 106 91 400 ≤ 10562474229480 :=
  rowsJ_le_of_split 105 106 (by norm_num) (by norm_num) rows225C_474 c105_8 (by norm_num)

theorem c105_6 : rowsJ 105 106 88 400 ≤ 12365948315389 :=
  rowsJ_le_of_split 105 106 (by norm_num) (by norm_num) rows225C_473 c105_7 (by norm_num)

theorem c105_5 : rowsJ 105 106 84 400 ≤ 12951783486377 :=
  rowsJ_le_of_split 105 106 (by norm_num) (by norm_num) rows225C_472 c105_6 (by norm_num)

theorem c105_4 : rowsJ 105 106 79 400 ≤ 17404549220738 :=
  rowsJ_le_of_split 105 106 (by norm_num) (by norm_num) rows225C_471 c105_5 (by norm_num)

theorem c105_3 : rowsJ 105 106 56 400 ≤ 205763310455280 :=
  rowsJ_le_of_split 105 106 (by norm_num) (by norm_num) rows225C_470 c105_4 (by norm_num)

theorem c105_2 : rowsJ 105 106 44 400 ≤ 455206478557440 :=
  rowsJ_le_of_split 105 106 (by norm_num) (by norm_num) rows225C_469 c105_3 (by norm_num)

theorem c105_1 : rowsJ 105 106 35 400 ≤ 618328830781203 :=
  rowsJ_le_of_split 105 106 (by norm_num) (by norm_num) rows225C_468 c105_2 (by norm_num)

theorem c105_0 : rowsJ 105 106 0 400 ≤ 691115042299406 :=
  rowsJ_le_of_split 105 106 (by norm_num) (by norm_num) rows225C_467 c105_1 (by norm_num)

theorem hr105 : rows 105 106 ≤ 691115042299406 := rows_le_of_rowsJ 105 106 c105_0

theorem c106_11 : rowsJ 106 107 101 400 ≤ 1948531577889 :=
  rowsJ_le_of_split 106 107 (by norm_num) (by norm_num) rows225C_491 rows225C_492 (by norm_num)

theorem c106_10 : rowsJ 106 107 98 400 ≤ 3413754882426 :=
  rowsJ_le_of_split 106 107 (by norm_num) (by norm_num) rows225C_490 c106_11 (by norm_num)

theorem c106_9 : rowsJ 106 107 95 400 ≤ 5438739342763 :=
  rowsJ_le_of_split 106 107 (by norm_num) (by norm_num) rows225C_489 c106_10 (by norm_num)

theorem c106_8 : rowsJ 106 107 93 400 ≤ 7132717662543 :=
  rowsJ_le_of_split 106 107 (by norm_num) (by norm_num) rows225C_488 c106_9 (by norm_num)

theorem c106_7 : rowsJ 106 107 91 400 ≤ 9127117723999 :=
  rowsJ_le_of_split 106 107 (by norm_num) (by norm_num) rows225C_487 c106_8 (by norm_num)

theorem c106_6 : rowsJ 106 107 88 400 ≤ 10918375587043 :=
  rowsJ_le_of_split 106 107 (by norm_num) (by norm_num) rows225C_486 c106_7 (by norm_num)

theorem c106_5 : rowsJ 106 107 85 400 ≤ 11396081046852 :=
  rowsJ_le_of_split 106 107 (by norm_num) (by norm_num) rows225C_485 c106_6 (by norm_num)

theorem c106_4 : rowsJ 106 107 80 400 ≤ 13167685616224 :=
  rowsJ_le_of_split 106 107 (by norm_num) (by norm_num) rows225C_484 c106_5 (by norm_num)

theorem c106_3 : rowsJ 106 107 57 400 ≤ 174225501389128 :=
  rowsJ_le_of_split 106 107 (by norm_num) (by norm_num) rows225C_483 c106_4 (by norm_num)

theorem c106_2 : rowsJ 106 107 44 400 ≤ 429536064414183 :=
  rowsJ_le_of_split 106 107 (by norm_num) (by norm_num) rows225C_482 c106_3 (by norm_num)

theorem c106_1 : rowsJ 106 107 35 400 ≤ 598234904514228 :=
  rowsJ_le_of_split 106 107 (by norm_num) (by norm_num) rows225C_481 c106_2 (by norm_num)

theorem c106_0 : rowsJ 106 107 0 400 ≤ 667400712208927 :=
  rowsJ_le_of_split 106 107 (by norm_num) (by norm_num) rows225C_480 c106_1 (by norm_num)

theorem hr106 : rows 106 107 ≤ 667400712208927 := rows_le_of_rowsJ 106 107 c106_0

theorem c107_11 : rowsJ 107 108 102 400 ≤ 1901390100060 :=
  rowsJ_le_of_split 107 108 (by norm_num) (by norm_num) rows225C_504 rows225C_505 (by norm_num)

theorem c107_10 : rowsJ 107 108 99 400 ≤ 2875333693576 :=
  rowsJ_le_of_split 107 108 (by norm_num) (by norm_num) rows225C_503 c107_11 (by norm_num)

theorem c107_9 : rowsJ 107 108 96 400 ≤ 4318665453538 :=
  rowsJ_le_of_split 107 108 (by norm_num) (by norm_num) rows225C_502 c107_10 (by norm_num)

theorem c107_8 : rowsJ 107 108 93 400 ≤ 6311873272945 :=
  rowsJ_le_of_split 107 108 (by norm_num) (by norm_num) rows225C_501 c107_9 (by norm_num)

theorem c107_7 : rowsJ 107 108 91 400 ≤ 7978732238699 :=
  rowsJ_le_of_split 107 108 (by norm_num) (by norm_num) rows225C_500 c107_8 (by norm_num)

theorem c107_6 : rowsJ 107 108 88 400 ≤ 9757971514875 :=
  rowsJ_le_of_split 107 108 (by norm_num) (by norm_num) rows225C_499 c107_7 (by norm_num)

theorem c107_5 : rowsJ 107 108 85 400 ≤ 10232890302131 :=
  rowsJ_le_of_split 107 108 (by norm_num) (by norm_num) rows225C_498 c107_6 (by norm_num)

theorem c107_4 : rowsJ 107 108 81 400 ≤ 10606306871751 :=
  rowsJ_le_of_split 107 108 (by norm_num) (by norm_num) rows225C_497 c107_5 (by norm_num)

theorem c107_3 : rowsJ 107 108 61 400 ≤ 110047700205437 :=
  rowsJ_le_of_split 107 108 (by norm_num) (by norm_num) rows225C_496 c107_4 (by norm_num)

theorem c107_2 : rowsJ 107 108 45 400 ≤ 381027469961574 :=
  rowsJ_le_of_split 107 108 (by norm_num) (by norm_num) rows225C_495 c107_3 (by norm_num)

theorem c107_1 : rowsJ 107 108 35 400 ≤ 579235589521114 :=
  rowsJ_le_of_split 107 108 (by norm_num) (by norm_num) rows225C_494 c107_2 (by norm_num)

theorem c107_0 : rowsJ 107 108 0 400 ≤ 645479379539149 :=
  rowsJ_le_of_split 107 108 (by norm_num) (by norm_num) rows225C_493 c107_1 (by norm_num)

theorem hr107 : rows 107 108 ≤ 645479379539149 := rows_le_of_rowsJ 107 108 c107_0

theorem c108_12 : rowsJ 108 109 105 400 ≤ 2138638116958 :=
  rowsJ_le_of_split 108 109 (by norm_num) (by norm_num) rows225C_518 rows225C_519 (by norm_num)

theorem c108_11 : rowsJ 108 109 102 400 ≤ 2661729597144 :=
  rowsJ_le_of_split 108 109 (by norm_num) (by norm_num) rows225C_517 c108_12 (by norm_num)

theorem c108_10 : rowsJ 108 109 99 400 ≤ 3358470570312 :=
  rowsJ_le_of_split 108 109 (by norm_num) (by norm_num) rows225C_516 c108_11 (by norm_num)

theorem c108_9 : rowsJ 108 109 96 400 ≤ 4462108218045 :=
  rowsJ_le_of_split 108 109 (by norm_num) (by norm_num) rows225C_515 c108_10 (by norm_num)

theorem c108_8 : rowsJ 108 109 93 400 ≤ 6057004160855 :=
  rowsJ_le_of_split 108 109 (by norm_num) (by norm_num) rows225C_514 c108_9 (by norm_num)

theorem c108_7 : rowsJ 108 109 91 400 ≤ 7426762117384 :=
  rowsJ_le_of_split 108 109 (by norm_num) (by norm_num) rows225C_513 c108_8 (by norm_num)

theorem c108_6 : rowsJ 108 109 88 400 ≤ 9194182775542 :=
  rowsJ_le_of_split 108 109 (by norm_num) (by norm_num) rows225C_512 c108_7 (by norm_num)

theorem c108_5 : rowsJ 108 109 85 400 ≤ 9665685461649 :=
  rowsJ_le_of_split 108 109 (by norm_num) (by norm_num) rows225C_511 c108_6 (by norm_num)

theorem c108_4 : rowsJ 108 109 81 400 ≤ 9770996174099 :=
  rowsJ_le_of_split 108 109 (by norm_num) (by norm_num) rows225C_510 c108_5 (by norm_num)

theorem c108_3 : rowsJ 108 109 64 400 ≤ 71486996805727 :=
  rowsJ_le_of_split 108 109 (by norm_num) (by norm_num) rows225C_509 c108_4 (by norm_num)

theorem c108_2 : rowsJ 108 109 45 400 ≤ 358349445355318 :=
  rowsJ_le_of_split 108 109 (by norm_num) (by norm_num) rows225C_508 c108_3 (by norm_num)

theorem c108_1 : rowsJ 108 109 35 400 ≤ 559855134587608 :=
  rowsJ_le_of_split 108 109 (by norm_num) (by norm_num) rows225C_507 c108_2 (by norm_num)

theorem c108_0 : rowsJ 108 109 0 400 ≤ 624091667655873 :=
  rowsJ_le_of_split 108 109 (by norm_num) (by norm_num) rows225C_506 c108_1 (by norm_num)

theorem hr108 : rows 108 109 ≤ 624091667655873 := rows_le_of_rowsJ 108 109 c108_0

theorem c109_12 : rowsJ 109 110 106 400 ≤ 3373385598978 :=
  rowsJ_le_of_split 109 110 (by norm_num) (by norm_num) rows225C_532 rows225C_533 (by norm_num)

theorem c109_11 : rowsJ 109 110 103 400 ≤ 4069607041979 :=
  rowsJ_le_of_split 109 110 (by norm_num) (by norm_num) rows225C_531 c109_12 (by norm_num)

theorem c109_10 : rowsJ 109 110 100 400 ≤ 4457489346126 :=
  rowsJ_le_of_split 109 110 (by norm_num) (by norm_num) rows225C_530 c109_11 (by norm_num)

theorem c109_9 : rowsJ 109 110 97 400 ≤ 5144032266611 :=
  rowsJ_le_of_split 109 110 (by norm_num) (by norm_num) rows225C_529 c109_10 (by norm_num)

theorem c109_8 : rowsJ 109 110 94 400 ≤ 6231394609460 :=
  rowsJ_le_of_split 109 110 (by norm_num) (by norm_num) rows225C_528 c109_9 (by norm_num)

theorem c109_7 : rowsJ 109 110 91 400 ≤ 7801087821481 :=
  rowsJ_le_of_split 109 110 (by norm_num) (by norm_num) rows225C_527 c109_8 (by norm_num)

theorem c109_6 : rowsJ 109 110 88 400 ≤ 9418334448027 :=
  rowsJ_le_of_split 109 110 (by norm_num) (by norm_num) rows225C_526 c109_7 (by norm_num)

theorem c109_5 : rowsJ 109 110 85 400 ≤ 9887138591394 :=
  rowsJ_le_of_split 109 110 (by norm_num) (by norm_num) rows225C_525 c109_6 (by norm_num)

theorem c109_4 : rowsJ 109 110 81 400 ≤ 9901684839020 :=
  rowsJ_le_of_split 109 110 (by norm_num) (by norm_num) rows225C_524 c109_5 (by norm_num)

theorem c109_3 : rowsJ 109 110 68 400 ≤ 38343229724102 :=
  rowsJ_le_of_split 109 110 (by norm_num) (by norm_num) rows225C_523 c109_4 (by norm_num)

theorem c109_2 : rowsJ 109 110 45 400 ≤ 337200037178395 :=
  rowsJ_le_of_split 109 110 (by norm_num) (by norm_num) rows225C_522 c109_3 (by norm_num)

theorem c109_1 : rowsJ 109 110 35 400 ≤ 542054955251142 :=
  rowsJ_le_of_split 109 110 (by norm_num) (by norm_num) rows225C_521 c109_2 (by norm_num)

theorem c109_0 : rowsJ 109 110 0 400 ≤ 605003189721961 :=
  rowsJ_le_of_split 109 110 (by norm_num) (by norm_num) rows225C_520 c109_1 (by norm_num)

theorem hr109 : rows 109 110 ≤ 605003189721961 := rows_le_of_rowsJ 109 110 c109_0

theorem c110_12 : rowsJ 110 111 106 400 ≤ 5585409773381 :=
  rowsJ_le_of_split 110 111 (by norm_num) (by norm_num) rows225C_546 rows225C_547 (by norm_num)

theorem c110_11 : rowsJ 110 111 103 400 ≤ 6368636436735 :=
  rowsJ_le_of_split 110 111 (by norm_num) (by norm_num) rows225C_545 c110_12 (by norm_num)

theorem c110_10 : rowsJ 110 111 100 400 ≤ 6613767660547 :=
  rowsJ_le_of_split 110 111 (by norm_num) (by norm_num) rows225C_544 c110_11 (by norm_num)

theorem c110_9 : rowsJ 110 111 97 400 ≤ 7073269579550 :=
  rowsJ_le_of_split 110 111 (by norm_num) (by norm_num) rows225C_543 c110_10 (by norm_num)

theorem c110_8 : rowsJ 110 111 94 400 ≤ 7871319353926 :=
  rowsJ_le_of_split 110 111 (by norm_num) (by norm_num) rows225C_542 c110_9 (by norm_num)

theorem c110_7 : rowsJ 110 111 91 400 ≤ 9093313037027 :=
  rowsJ_le_of_split 110 111 (by norm_num) (by norm_num) rows225C_541 c110_8 (by norm_num)

theorem c110_6 : rowsJ 110 111 88 400 ≤ 10575054166327 :=
  rowsJ_le_of_split 110 111 (by norm_num) (by norm_num) rows225C_540 c110_7 (by norm_num)

theorem c110_5 : rowsJ 110 111 85 400 ≤ 11041190844913 :=
  rowsJ_le_of_split 110 111 (by norm_num) (by norm_num) rows225C_539 c110_6 (by norm_num)

theorem c110_4 : rowsJ 110 111 81 400 ≤ 11055653697131 :=
  rowsJ_le_of_split 110 111 (by norm_num) (by norm_num) rows225C_538 c110_5 (by norm_num)

theorem c110_3 : rowsJ 110 111 72 400 ≤ 20061131388326 :=
  rowsJ_le_of_split 110 111 (by norm_num) (by norm_num) rows225C_537 c110_4 (by norm_num)

theorem c110_2 : rowsJ 110 111 45 400 ≤ 317686572508424 :=
  rowsJ_le_of_split 110 111 (by norm_num) (by norm_num) rows225C_536 c110_3 (by norm_num)

theorem c110_1 : rowsJ 110 111 35 400 ≤ 524180031987444 :=
  rowsJ_le_of_split 110 111 (by norm_num) (by norm_num) rows225C_535 c110_2 (by norm_num)

theorem c110_0 : rowsJ 110 111 0 400 ≤ 586632531615986 :=
  rowsJ_le_of_split 110 111 (by norm_num) (by norm_num) rows225C_534 c110_1 (by norm_num)

theorem hr110 : rows 110 111 ≤ 586632531615986 := rows_le_of_rowsJ 110 111 c110_0

theorem c111_12 : rowsJ 111 112 106 400 ≤ 8617810595818 :=
  rowsJ_le_of_split 111 112 (by norm_num) (by norm_num) rows225C_560 rows225C_561 (by norm_num)

theorem c111_11 : rowsJ 111 112 103 400 ≤ 9598011824506 :=
  rowsJ_le_of_split 111 112 (by norm_num) (by norm_num) rows225C_559 c111_12 (by norm_num)

theorem c111_10 : rowsJ 111 112 100 400 ≤ 9785389927555 :=
  rowsJ_le_of_split 111 112 (by norm_num) (by norm_num) rows225C_558 c111_11 (by norm_num)

theorem c111_9 : rowsJ 111 112 97 400 ≤ 10063682014208 :=
  rowsJ_le_of_split 111 112 (by norm_num) (by norm_num) rows225C_557 c111_10 (by norm_num)

theorem c111_8 : rowsJ 111 112 94 400 ≤ 10617014371794 :=
  rowsJ_le_of_split 111 112 (by norm_num) (by norm_num) rows225C_556 c111_9 (by norm_num)

theorem c111_7 : rowsJ 111 112 91 400 ≤ 11535098448438 :=
  rowsJ_le_of_split 111 112 (by norm_num) (by norm_num) rows225C_555 c111_8 (by norm_num)

theorem c111_6 : rowsJ 111 112 88 400 ≤ 12780210052970 :=
  rowsJ_le_of_split 111 112 (by norm_num) (by norm_num) rows225C_554 c111_7 (by norm_num)

theorem c111_5 : rowsJ 111 112 85 400 ≤ 13243051596577 :=
  rowsJ_le_of_split 111 112 (by norm_num) (by norm_num) rows225C_553 c111_6 (by norm_num)

theorem c111_4 : rowsJ 111 112 81 400 ≤ 13257432004167 :=
  rowsJ_le_of_split 111 112 (by norm_num) (by norm_num) rows225C_552 c111_5 (by norm_num)

theorem c111_3 : rowsJ 111 112 74 400 ≤ 16228270059812 :=
  rowsJ_le_of_split 111 112 (by norm_num) (by norm_num) rows225C_551 c111_4 (by norm_num)

theorem c111_2 : rowsJ 111 112 46 400 ≤ 280068604079540 :=
  rowsJ_le_of_split 111 112 (by norm_num) (by norm_num) rows225C_550 c111_3 (by norm_num)

theorem c111_1 : rowsJ 111 112 35 400 ≤ 508095977598105 :=
  rowsJ_le_of_split 111 112 (by norm_num) (by norm_num) rows225C_549 c111_2 (by norm_num)

theorem c111_0 : rowsJ 111 112 0 400 ≤ 570848882213249 :=
  rowsJ_le_of_split 111 112 (by norm_num) (by norm_num) rows225C_548 c111_1 (by norm_num)

theorem hr111 : rows 111 112 ≤ 570848882213249 := rows_le_of_rowsJ 111 112 c111_0

theorem c112_12 : rowsJ 112 113 106 400 ≤ 12437098933694 :=
  rowsJ_le_of_split 112 113 (by norm_num) (by norm_num) rows225C_574 rows225C_575 (by norm_num)

theorem c112_11 : rowsJ 112 113 103 400 ≤ 13662834636818 :=
  rowsJ_le_of_split 112 113 (by norm_num) (by norm_num) rows225C_573 c112_12 (by norm_num)

theorem c112_10 : rowsJ 112 113 100 400 ≤ 13840955780536 :=
  rowsJ_le_of_split 112 113 (by norm_num) (by norm_num) rows225C_572 c112_11 (by norm_num)

theorem c112_9 : rowsJ 112 113 97 400 ≤ 13983635402545 :=
  rowsJ_le_of_split 112 113 (by norm_num) (by norm_num) rows225C_571 c112_10 (by norm_num)

theorem c112_8 : rowsJ 112 113 94 400 ≤ 14337227081330 :=
  rowsJ_le_of_split 112 113 (by norm_num) (by norm_num) rows225C_570 c112_9 (by norm_num)

theorem c112_7 : rowsJ 112 113 91 400 ≤ 14994730571308 :=
  rowsJ_le_of_split 112 113 (by norm_num) (by norm_num) rows225C_569 c112_8 (by norm_num)

theorem c112_6 : rowsJ 112 113 88 400 ≤ 16031700678085 :=
  rowsJ_le_of_split 112 113 (by norm_num) (by norm_num) rows225C_568 c112_7 (by norm_num)

theorem c112_5 : rowsJ 112 113 85 400 ≤ 16491300514743 :=
  rowsJ_le_of_split 112 113 (by norm_num) (by norm_num) rows225C_567 c112_6 (by norm_num)

theorem c112_4 : rowsJ 112 113 81 400 ≤ 16505599412319 :=
  rowsJ_le_of_split 112 113 (by norm_num) (by norm_num) rows225C_566 c112_5 (by norm_num)

theorem c112_3 : rowsJ 112 113 74 400 ≤ 18275814573181 :=
  rowsJ_le_of_split 112 113 (by norm_num) (by norm_num) rows225C_565 c112_4 (by norm_num)

theorem c112_2 : rowsJ 112 113 46 400 ≤ 264924332681650 :=
  rowsJ_le_of_split 112 113 (by norm_num) (by norm_num) rows225C_564 c112_3 (by norm_num)

theorem c112_1 : rowsJ 112 113 35 400 ≤ 492018417165580 :=
  rowsJ_le_of_split 112 113 (by norm_num) (by norm_num) rows225C_563 c112_2 (by norm_num)

theorem c112_0 : rowsJ 112 113 0 400 ≤ 555890647174645 :=
  rowsJ_le_of_split 112 113 (by norm_num) (by norm_num) rows225C_562 c112_1 (by norm_num)

theorem hr112 : rows 112 113 ≤ 555890647174645 := rows_le_of_rowsJ 112 113 c112_0

theorem c113_12 : rowsJ 113 114 106 400 ≤ 17278110878127 :=
  rowsJ_le_of_split 113 114 (by norm_num) (by norm_num) rows225C_588 rows225C_589 (by norm_num)

theorem c113_11 : rowsJ 113 114 103 400 ≤ 18801878608297 :=
  rowsJ_le_of_split 113 114 (by norm_num) (by norm_num) rows225C_587 c113_12 (by norm_num)

theorem c113_10 : rowsJ 113 114 100 400 ≤ 19077023319201 :=
  rowsJ_le_of_split 113 114 (by norm_num) (by norm_num) rows225C_586 c113_11 (by norm_num)

theorem c113_9 : rowsJ 113 114 97 400 ≤ 19129484350202 :=
  rowsJ_le_of_split 113 114 (by norm_num) (by norm_num) rows225C_585 c113_10 (by norm_num)

theorem c113_8 : rowsJ 113 114 94 400 ≤ 19328070435826 :=
  rowsJ_le_of_split 113 114 (by norm_num) (by norm_num) rows225C_584 c113_9 (by norm_num)

theorem c113_7 : rowsJ 113 114 91 400 ≤ 19768585863753 :=
  rowsJ_le_of_split 113 114 (by norm_num) (by norm_num) rows225C_583 c113_8 (by norm_num)

theorem c113_6 : rowsJ 113 114 88 400 ≤ 20530528959172 :=
  rowsJ_le_of_split 113 114 (by norm_num) (by norm_num) rows225C_582 c113_7 (by norm_num)

theorem c113_5 : rowsJ 113 114 85 400 ≤ 20986939857439 :=
  rowsJ_le_of_split 113 114 (by norm_num) (by norm_num) rows225C_581 c113_6 (by norm_num)

theorem c113_4 : rowsJ 113 114 81 400 ≤ 21001158163813 :=
  rowsJ_le_of_split 113 114 (by norm_num) (by norm_num) rows225C_580 c113_5 (by norm_num)

theorem c113_3 : rowsJ 113 114 75 400 ≤ 21362616008287 :=
  rowsJ_le_of_split 113 114 (by norm_num) (by norm_num) rows225C_579 c113_4 (by norm_num)

theorem c113_2 : rowsJ 113 114 47 400 ≤ 234208185110189 :=
  rowsJ_le_of_split 113 114 (by norm_num) (by norm_num) rows225C_578 c113_3 (by norm_num)

theorem c113_1 : rowsJ 113 114 35 400 ≤ 477911902323519 :=
  rowsJ_le_of_split 113 114 (by norm_num) (by norm_num) rows225C_577 c113_2 (by norm_num)

theorem c113_0 : rowsJ 113 114 0 400 ≤ 543573306278250 :=
  rowsJ_le_of_split 113 114 (by norm_num) (by norm_num) rows225C_576 c113_1 (by norm_num)

theorem hr113 : rows 113 114 ≤ 543573306278250 := rows_le_of_rowsJ 113 114 c113_0

theorem c114_13 : rowsJ 114 115 109 400 ≤ 18990819066129 :=
  rowsJ_le_of_split 114 115 (by norm_num) (by norm_num) rows225C_603 rows225C_604 (by norm_num)

theorem c114_12 : rowsJ 114 115 105 400 ≤ 23927251855100 :=
  rowsJ_le_of_split 114 115 (by norm_num) (by norm_num) rows225C_602 c114_13 (by norm_num)

theorem c114_11 : rowsJ 114 115 102 400 ≤ 25161515641530 :=
  rowsJ_le_of_split 114 115 (by norm_num) (by norm_num) rows225C_601 c114_12 (by norm_num)

theorem c114_10 : rowsJ 114 115 99 400 ≤ 25320511794563 :=
  rowsJ_le_of_split 114 115 (by norm_num) (by norm_num) rows225C_600 c114_11 (by norm_num)

theorem c114_9 : rowsJ 114 115 96 400 ≤ 25342783862039 :=
  rowsJ_le_of_split 114 115 (by norm_num) (by norm_num) rows225C_599 c114_10 (by norm_num)

theorem c114_8 : rowsJ 114 115 93 400 ≤ 25481465488111 :=
  rowsJ_le_of_split 114 115 (by norm_num) (by norm_num) rows225C_598 c114_9 (by norm_num)

theorem c114_7 : rowsJ 114 115 90 400 ≤ 25825484052622 :=
  rowsJ_le_of_split 114 115 (by norm_num) (by norm_num) rows225C_597 c114_8 (by norm_num)

theorem c114_6 : rowsJ 114 115 87 400 ≤ 26462187488452 :=
  rowsJ_le_of_split 114 115 (by norm_num) (by norm_num) rows225C_596 c114_7 (by norm_num)

theorem c114_5 : rowsJ 114 115 84 400 ≤ 26679669125815 :=
  rowsJ_le_of_split 114 115 (by norm_num) (by norm_num) rows225C_595 c114_6 (by norm_num)

theorem c114_4 : rowsJ 114 115 81 400 ≤ 26679669125815 :=
  rowsJ_le_of_split 114 115 (by norm_num) (by norm_num) rows225C_594 c114_5 (by norm_num)

theorem c114_3 : rowsJ 114 115 76 400 ≤ 26679669125815 :=
  rowsJ_le_of_split 114 115 (by norm_num) (by norm_num) rows225C_593 c114_4 (by norm_num)

theorem c114_2 : rowsJ 114 115 48 400 ≤ 207711318442946 :=
  rowsJ_le_of_split 114 115 (by norm_num) (by norm_num) rows225C_592 c114_3 (by norm_num)

theorem c114_1 : rowsJ 114 115 35 400 ≤ 463881333465192 :=
  rowsJ_le_of_split 114 115 (by norm_num) (by norm_num) rows225C_591 c114_2 (by norm_num)

theorem c114_0 : rowsJ 114 115 0 400 ≤ 532235598055031 :=
  rowsJ_le_of_split 114 115 (by norm_num) (by norm_num) rows225C_590 c114_1 (by norm_num)

theorem hr114 : rows 114 115 ≤ 532235598055031 := rows_le_of_rowsJ 114 115 c114_0

theorem c115_13 : rowsJ 115 116 110 400 ≤ 23421945390523 :=
  rowsJ_le_of_split 115 116 (by norm_num) (by norm_num) rows225C_618 rows225C_619 (by norm_num)

theorem c115_12 : rowsJ 115 116 106 400 ≤ 30220930769114 :=
  rowsJ_le_of_split 115 116 (by norm_num) (by norm_num) rows225C_617 c115_13 (by norm_num)

theorem c115_11 : rowsJ 115 116 102 400 ≤ 32670861061528 :=
  rowsJ_le_of_split 115 116 (by norm_num) (by norm_num) rows225C_616 c115_12 (by norm_num)

theorem c115_10 : rowsJ 115 116 99 400 ≤ 32952828401564 :=
  rowsJ_le_of_split 115 116 (by norm_num) (by norm_num) rows225C_615 c115_11 (by norm_num)

theorem c115_9 : rowsJ 115 116 96 400 ≤ 32952828401564 :=
  rowsJ_le_of_split 115 116 (by norm_num) (by norm_num) rows225C_614 c115_10 (by norm_num)

theorem c115_8 : rowsJ 115 116 93 400 ≤ 33003822196116 :=
  rowsJ_le_of_split 115 116 (by norm_num) (by norm_num) rows225C_613 c115_9 (by norm_num)

theorem c115_7 : rowsJ 115 116 90 400 ≤ 33197036347887 :=
  rowsJ_le_of_split 115 116 (by norm_num) (by norm_num) rows225C_612 c115_8 (by norm_num)

theorem c115_6 : rowsJ 115 116 87 400 ≤ 33624158530145 :=
  rowsJ_le_of_split 115 116 (by norm_num) (by norm_num) rows225C_611 c115_7 (by norm_num)

theorem c115_5 : rowsJ 115 116 84 400 ≤ 33840448416239 :=
  rowsJ_le_of_split 115 116 (by norm_num) (by norm_num) rows225C_610 c115_6 (by norm_num)

theorem c115_4 : rowsJ 115 116 81 400 ≤ 33840448416239 :=
  rowsJ_le_of_split 115 116 (by norm_num) (by norm_num) rows225C_609 c115_5 (by norm_num)

theorem c115_3 : rowsJ 115 116 76 400 ≤ 33840448416239 :=
  rowsJ_le_of_split 115 116 (by norm_num) (by norm_num) rows225C_608 c115_4 (by norm_num)

theorem c115_2 : rowsJ 115 116 49 400 ≤ 185670992414557 :=
  rowsJ_le_of_split 115 116 (by norm_num) (by norm_num) rows225C_607 c115_3 (by norm_num)

theorem c115_1 : rowsJ 115 116 35 400 ≤ 452035201833878 :=
  rowsJ_le_of_split 115 116 (by norm_num) (by norm_num) rows225C_606 c115_2 (by norm_num)

theorem c115_0 : rowsJ 115 116 0 400 ≤ 523780522347557 :=
  rowsJ_le_of_split 115 116 (by norm_num) (by norm_num) rows225C_605 c115_1 (by norm_num)

theorem hr115 : rows 115 116 ≤ 523780522347557 := rows_le_of_rowsJ 115 116 c115_0

theorem c116_13 : rowsJ 116 117 110 400 ≤ 31154512112772 :=
  rowsJ_le_of_split 116 117 (by norm_num) (by norm_num) rows225C_633 rows225C_634 (by norm_num)

theorem c116_12 : rowsJ 116 117 106 400 ≤ 38561775739565 :=
  rowsJ_le_of_split 116 117 (by norm_num) (by norm_num) rows225C_632 c116_13 (by norm_num)

theorem c116_11 : rowsJ 116 117 102 400 ≤ 41380824636185 :=
  rowsJ_le_of_split 116 117 (by norm_num) (by norm_num) rows225C_631 c116_12 (by norm_num)

theorem c116_10 : rowsJ 116 117 99 400 ≤ 41790561000848 :=
  rowsJ_le_of_split 116 117 (by norm_num) (by norm_num) rows225C_630 c116_11 (by norm_num)

theorem c116_9 : rowsJ 116 117 96 400 ≤ 41790561000848 :=
  rowsJ_le_of_split 116 117 (by norm_num) (by norm_num) rows225C_629 c116_10 (by norm_num)

theorem c116_8 : rowsJ 116 117 93 400 ≤ 41797816546467 :=
  rowsJ_le_of_split 116 117 (by norm_num) (by norm_num) rows225C_628 c116_9 (by norm_num)

theorem c116_7 : rowsJ 116 117 90 400 ≤ 41883539772222 :=
  rowsJ_le_of_split 116 117 (by norm_num) (by norm_num) rows225C_627 c116_8 (by norm_num)

theorem c116_6 : rowsJ 116 117 87 400 ≤ 42142727913082 :=
  rowsJ_le_of_split 116 117 (by norm_num) (by norm_num) rows225C_626 c116_7 (by norm_num)

theorem c116_5 : rowsJ 116 117 84 400 ≤ 42357183077281 :=
  rowsJ_le_of_split 116 117 (by norm_num) (by norm_num) rows225C_625 c116_6 (by norm_num)

theorem c116_4 : rowsJ 116 117 81 400 ≤ 42357183077281 :=
  rowsJ_le_of_split 116 117 (by norm_num) (by norm_num) rows225C_624 c116_5 (by norm_num)

theorem c116_3 : rowsJ 116 117 76 400 ≤ 42357183077281 :=
  rowsJ_le_of_split 116 117 (by norm_num) (by norm_num) rows225C_623 c116_4 (by norm_num)

theorem c116_2 : rowsJ 116 117 50 400 ≤ 167893866956839 :=
  rowsJ_le_of_split 116 117 (by norm_num) (by norm_num) rows225C_622 c116_3 (by norm_num)

theorem c116_1 : rowsJ 116 117 35 400 ≤ 440399572638278 :=
  rowsJ_le_of_split 116 117 (by norm_num) (by norm_num) rows225C_621 c116_2 (by norm_num)

theorem c116_0 : rowsJ 116 117 0 400 ≤ 516313289575828 :=
  rowsJ_le_of_split 116 117 (by norm_num) (by norm_num) rows225C_620 c116_1 (by norm_num)

theorem hr116 : rows 116 117 ≤ 516313289575828 := rows_le_of_rowsJ 116 117 c116_0

theorem c117_13 : rowsJ 117 118 110 400 ≤ 134876084755545 :=
  rowsJ_le_of_split 117 118 (by norm_num) (by norm_num) rows225C_648 rows225C_649 (by norm_num)

theorem c117_12 : rowsJ 117 118 106 400 ≤ 142945625608493 :=
  rowsJ_le_of_split 117 118 (by norm_num) (by norm_num) rows225C_647 c117_13 (by norm_num)

theorem c117_11 : rowsJ 117 118 102 400 ≤ 146182062074030 :=
  rowsJ_le_of_split 117 118 (by norm_num) (by norm_num) rows225C_646 c117_12 (by norm_num)

theorem c117_10 : rowsJ 117 118 99 400 ≤ 146763076809358 :=
  rowsJ_le_of_split 117 118 (by norm_num) (by norm_num) rows225C_645 c117_11 (by norm_num)

theorem c117_9 : rowsJ 117 118 96 400 ≤ 146783449077412 :=
  rowsJ_le_of_split 117 118 (by norm_num) (by norm_num) rows225C_644 c117_10 (by norm_num)

theorem c117_8 : rowsJ 117 118 93 400 ≤ 146783449077412 :=
  rowsJ_le_of_split 117 118 (by norm_num) (by norm_num) rows225C_643 c117_9 (by norm_num)

theorem c117_7 : rowsJ 117 118 90 400 ≤ 146804817571636 :=
  rowsJ_le_of_split 117 118 (by norm_num) (by norm_num) rows225C_642 c117_8 (by norm_num)

theorem c117_6 : rowsJ 117 118 87 400 ≤ 146938048422952 :=
  rowsJ_le_of_split 117 118 (by norm_num) (by norm_num) rows225C_641 c117_7 (by norm_num)

theorem c117_5 : rowsJ 117 118 84 400 ≤ 147096973756414 :=
  rowsJ_le_of_split 117 118 (by norm_num) (by norm_num) rows225C_640 c117_6 (by norm_num)

theorem c117_4 : rowsJ 117 118 81 400 ≤ 147096973756414 :=
  rowsJ_le_of_split 117 118 (by norm_num) (by norm_num) rows225C_639 c117_5 (by norm_num)

theorem c117_3 : rowsJ 117 118 76 400 ≤ 147096973756414 :=
  rowsJ_le_of_split 117 118 (by norm_num) (by norm_num) rows225C_638 c117_4 (by norm_num)

theorem c117_2 : rowsJ 117 118 51 400 ≤ 249174103064013 :=
  rowsJ_le_of_split 117 118 (by norm_num) (by norm_num) rows225C_637 c117_3 (by norm_num)

theorem c117_1 : rowsJ 117 118 35 400 ≤ 525632610762144 :=
  rowsJ_le_of_split 117 118 (by norm_num) (by norm_num) rows225C_636 c117_2 (by norm_num)

theorem c117_0 : rowsJ 117 118 0 400 ≤ 606501423739795 :=
  rowsJ_le_of_split 117 118 (by norm_num) (by norm_num) rows225C_635 c117_1 (by norm_num)

theorem hr117 : rows 117 118 ≤ 606501423739795 := rows_le_of_rowsJ 117 118 c117_0

theorem c118_13 : rowsJ 118 119 109 400 ≤ 334577306487333 :=
  rowsJ_le_of_split 118 119 (by norm_num) (by norm_num) rows225C_663 rows225C_664 (by norm_num)

theorem c118_12 : rowsJ 118 119 105 400 ≤ 341797012468267 :=
  rowsJ_le_of_split 118 119 (by norm_num) (by norm_num) rows225C_662 c118_13 (by norm_num)

theorem c118_11 : rowsJ 118 119 101 400 ≤ 344507154190864 :=
  rowsJ_le_of_split 118 119 (by norm_num) (by norm_num) rows225C_661 c118_12 (by norm_num)

theorem c118_10 : rowsJ 118 119 98 400 ≤ 344905443098983 :=
  rowsJ_le_of_split 118 119 (by norm_num) (by norm_num) rows225C_660 c118_11 (by norm_num)

theorem c118_9 : rowsJ 118 119 95 400 ≤ 344905443098983 :=
  rowsJ_le_of_split 118 119 (by norm_num) (by norm_num) rows225C_659 c118_10 (by norm_num)

theorem c118_8 : rowsJ 118 119 92 400 ≤ 344905443098983 :=
  rowsJ_le_of_split 118 119 (by norm_num) (by norm_num) rows225C_658 c118_9 (by norm_num)

theorem c118_7 : rowsJ 118 119 89 400 ≤ 344912506556992 :=
  rowsJ_le_of_split 118 119 (by norm_num) (by norm_num) rows225C_657 c118_8 (by norm_num)

theorem c118_6 : rowsJ 118 119 86 400 ≤ 344996027703609 :=
  rowsJ_le_of_split 118 119 (by norm_num) (by norm_num) rows225C_656 c118_7 (by norm_num)

theorem c118_5 : rowsJ 118 119 83 400 ≤ 345071255510075 :=
  rowsJ_le_of_split 118 119 (by norm_num) (by norm_num) rows225C_655 c118_6 (by norm_num)

theorem c118_4 : rowsJ 118 119 80 400 ≤ 345071255510075 :=
  rowsJ_le_of_split 118 119 (by norm_num) (by norm_num) rows225C_654 c118_5 (by norm_num)

theorem c118_3 : rowsJ 118 119 76 400 ≤ 345071255510075 :=
  rowsJ_le_of_split 118 119 (by norm_num) (by norm_num) rows225C_653 c118_4 (by norm_num)

theorem c118_2 : rowsJ 118 119 54 400 ≤ 408234237925741 :=
  rowsJ_le_of_split 118 119 (by norm_num) (by norm_num) rows225C_652 c118_3 (by norm_num)

theorem c118_1 : rowsJ 118 119 35 400 ≤ 702912914049664 :=
  rowsJ_le_of_split 118 119 (by norm_num) (by norm_num) rows225C_651 c118_2 (by norm_num)

theorem c118_0 : rowsJ 118 119 0 400 ≤ 789549229061627 :=
  rowsJ_le_of_split 118 119 (by norm_num) (by norm_num) rows225C_650 c118_1 (by norm_num)

theorem hr118 : rows 118 119 ≤ 789549229061627 := rows_le_of_rowsJ 118 119 c118_0

theorem c119_13 : rowsJ 119 120 110 400 ≤ 430305327781008 :=
  rowsJ_le_of_split 119 120 (by norm_num) (by norm_num) rows225C_678 rows225C_679 (by norm_num)

theorem c119_12 : rowsJ 119 120 106 400 ≤ 439713937168282 :=
  rowsJ_le_of_split 119 120 (by norm_num) (by norm_num) rows225C_677 c119_13 (by norm_num)

theorem c119_11 : rowsJ 119 120 102 400 ≤ 443777705930632 :=
  rowsJ_le_of_split 119 120 (by norm_num) (by norm_num) rows225C_676 c119_12 (by norm_num)

theorem c119_10 : rowsJ 119 120 98 400 ≤ 444778823651016 :=
  rowsJ_le_of_split 119 120 (by norm_num) (by norm_num) rows225C_675 c119_11 (by norm_num)

theorem c119_9 : rowsJ 119 120 95 400 ≤ 444799716553798 :=
  rowsJ_le_of_split 119 120 (by norm_num) (by norm_num) rows225C_674 c119_10 (by norm_num)

theorem c119_8 : rowsJ 119 120 92 400 ≤ 444799716553798 :=
  rowsJ_le_of_split 119 120 (by norm_num) (by norm_num) rows225C_673 c119_9 (by norm_num)

theorem c119_7 : rowsJ 119 120 89 400 ≤ 444799716553798 :=
  rowsJ_le_of_split 119 120 (by norm_num) (by norm_num) rows225C_672 c119_8 (by norm_num)

theorem c119_6 : rowsJ 119 120 86 400 ≤ 444820538472105 :=
  rowsJ_le_of_split 119 120 (by norm_num) (by norm_num) rows225C_671 c119_7 (by norm_num)

theorem c119_5 : rowsJ 119 120 83 400 ≤ 444861847274498 :=
  rowsJ_le_of_split 119 120 (by norm_num) (by norm_num) rows225C_670 c119_6 (by norm_num)

theorem c119_4 : rowsJ 119 120 80 400 ≤ 444861847274498 :=
  rowsJ_le_of_split 119 120 (by norm_num) (by norm_num) rows225C_669 c119_5 (by norm_num)

theorem c119_3 : rowsJ 119 120 76 400 ≤ 444861847274498 :=
  rowsJ_le_of_split 119 120 (by norm_num) (by norm_num) rows225C_668 c119_4 (by norm_num)

theorem c119_2 : rowsJ 119 120 58 400 ≤ 473891527366898 :=
  rowsJ_le_of_split 119 120 (by norm_num) (by norm_num) rows225C_667 c119_3 (by norm_num)

theorem c119_1 : rowsJ 119 120 35 400 ≤ 782713196174043 :=
  rowsJ_le_of_split 119 120 (by norm_num) (by norm_num) rows225C_666 c119_2 (by norm_num)

theorem c119_0 : rowsJ 119 120 0 400 ≤ 875687710712350 :=
  rowsJ_le_of_split 119 120 (by norm_num) (by norm_num) rows225C_665 c119_1 (by norm_num)

theorem hr119 : rows 119 120 ≤ 875687710712350 := rows_le_of_rowsJ 119 120 c119_0

theorem c120_12 : rowsJ 120 121 106 400 ≤ 632304516321868 :=
  rowsJ_le_of_split 120 121 (by norm_num) (by norm_num) rows225C_692 rows225C_693 (by norm_num)

theorem c120_11 : rowsJ 120 121 102 400 ≤ 636778307144810 :=
  rowsJ_le_of_split 120 121 (by norm_num) (by norm_num) rows225C_691 c120_12 (by norm_num)

theorem c120_10 : rowsJ 120 121 98 400 ≤ 637966430983045 :=
  rowsJ_le_of_split 120 121 (by norm_num) (by norm_num) rows225C_690 c120_11 (by norm_num)

theorem c120_9 : rowsJ 120 121 95 400 ≤ 638009054423161 :=
  rowsJ_le_of_split 120 121 (by norm_num) (by norm_num) rows225C_689 c120_10 (by norm_num)

theorem c120_8 : rowsJ 120 121 92 400 ≤ 638009054423161 :=
  rowsJ_le_of_split 120 121 (by norm_num) (by norm_num) rows225C_688 c120_9 (by norm_num)

theorem c120_7 : rowsJ 120 121 89 400 ≤ 638009054423161 :=
  rowsJ_le_of_split 120 121 (by norm_num) (by norm_num) rows225C_687 c120_8 (by norm_num)

theorem c120_6 : rowsJ 120 121 86 400 ≤ 638009054423161 :=
  rowsJ_le_of_split 120 121 (by norm_num) (by norm_num) rows225C_686 c120_7 (by norm_num)

theorem c120_5 : rowsJ 120 121 83 400 ≤ 638029618929007 :=
  rowsJ_le_of_split 120 121 (by norm_num) (by norm_num) rows225C_685 c120_6 (by norm_num)

theorem c120_4 : rowsJ 120 121 80 400 ≤ 638029618929007 :=
  rowsJ_le_of_split 120 121 (by norm_num) (by norm_num) rows225C_684 c120_5 (by norm_num)

theorem c120_3 : rowsJ 120 121 76 400 ≤ 638029618929007 :=
  rowsJ_le_of_split 120 121 (by norm_num) (by norm_num) rows225C_683 c120_4 (by norm_num)

theorem c120_2 : rowsJ 120 121 67 400 ≤ 638936269286145 :=
  rowsJ_le_of_split 120 121 (by norm_num) (by norm_num) rows225C_682 c120_3 (by norm_num)

theorem c120_1 : rowsJ 120 121 35 400 ≤ 954711761728543 :=
  rowsJ_le_of_split 120 121 (by norm_num) (by norm_num) rows225C_681 c120_2 (by norm_num)

theorem c120_0 : rowsJ 120 121 0 400 ≤ 1054846955790975 :=
  rowsJ_le_of_split 120 121 (by norm_num) (by norm_num) rows225C_680 c120_1 (by norm_num)

theorem hr120 : rows 120 121 ≤ 1054846955790975 := rows_le_of_rowsJ 120 121 c120_0

theorem c121_12 : rowsJ 121 122 106 400 ≤ 726583646754856 :=
  rowsJ_le_of_split 121 122 (by norm_num) (by norm_num) rows225C_706 rows225C_707 (by norm_num)

theorem c121_11 : rowsJ 121 122 102 400 ≤ 731518840950561 :=
  rowsJ_le_of_split 121 122 (by norm_num) (by norm_num) rows225C_705 c121_12 (by norm_num)

theorem c121_10 : rowsJ 121 122 98 400 ≤ 732940229402544 :=
  rowsJ_le_of_split 121 122 (by norm_num) (by norm_num) rows225C_704 c121_11 (by norm_num)

theorem c121_9 : rowsJ 121 122 95 400 ≤ 733026238360206 :=
  rowsJ_le_of_split 121 122 (by norm_num) (by norm_num) rows225C_703 c121_10 (by norm_num)

theorem c121_8 : rowsJ 121 122 92 400 ≤ 733026238360206 :=
  rowsJ_le_of_split 121 122 (by norm_num) (by norm_num) rows225C_702 c121_9 (by norm_num)

theorem c121_7 : rowsJ 121 122 89 400 ≤ 733026238360206 :=
  rowsJ_le_of_split 121 122 (by norm_num) (by norm_num) rows225C_701 c121_8 (by norm_num)

theorem c121_6 : rowsJ 121 122 86 400 ≤ 733026238360206 :=
  rowsJ_le_of_split 121 122 (by norm_num) (by norm_num) rows225C_700 c121_7 (by norm_num)

theorem c121_5 : rowsJ 121 122 83 400 ≤ 733026238360206 :=
  rowsJ_le_of_split 121 122 (by norm_num) (by norm_num) rows225C_699 c121_6 (by norm_num)

theorem c121_4 : rowsJ 121 122 80 400 ≤ 733026238360206 :=
  rowsJ_le_of_split 121 122 (by norm_num) (by norm_num) rows225C_698 c121_5 (by norm_num)

theorem c121_3 : rowsJ 121 122 76 400 ≤ 733026238360206 :=
  rowsJ_le_of_split 121 122 (by norm_num) (by norm_num) rows225C_697 c121_4 (by norm_num)

theorem c121_2 : rowsJ 121 122 68 400 ≤ 733118838796602 :=
  rowsJ_le_of_split 121 122 (by norm_num) (by norm_num) rows225C_696 c121_3 (by norm_num)

theorem c121_1 : rowsJ 121 122 35 400 ≤ 1029303077202081 :=
  rowsJ_le_of_split 121 122 (by norm_num) (by norm_num) rows225C_695 c121_2 (by norm_num)

theorem c121_0 : rowsJ 121 122 0 400 ≤ 1137116762595884 :=
  rowsJ_le_of_split 121 122 (by norm_num) (by norm_num) rows225C_694 c121_1 (by norm_num)

theorem hr121 : rows 121 122 ≤ 1137116762595884 := rows_le_of_rowsJ 121 122 c121_0

theorem c122_12 : rowsJ 122 123 107 400 ≤ 912258992305756 :=
  rowsJ_le_of_split 122 123 (by norm_num) (by norm_num) rows225C_720 rows225C_721 (by norm_num)

theorem c122_11 : rowsJ 122 123 103 400 ≤ 918934497399822 :=
  rowsJ_le_of_split 122 123 (by norm_num) (by norm_num) rows225C_719 c122_12 (by norm_num)

theorem c122_10 : rowsJ 122 123 99 400 ≤ 921274335789030 :=
  rowsJ_le_of_split 122 123 (by norm_num) (by norm_num) rows225C_718 c122_11 (by norm_num)

theorem c122_9 : rowsJ 122 123 95 400 ≤ 921559085683060 :=
  rowsJ_le_of_split 122 123 (by norm_num) (by norm_num) rows225C_717 c122_10 (by norm_num)

theorem c122_8 : rowsJ 122 123 92 400 ≤ 921559085683060 :=
  rowsJ_le_of_split 122 123 (by norm_num) (by norm_num) rows225C_716 c122_9 (by norm_num)

theorem c122_7 : rowsJ 122 123 89 400 ≤ 921559085683060 :=
  rowsJ_le_of_split 122 123 (by norm_num) (by norm_num) rows225C_715 c122_8 (by norm_num)

theorem c122_6 : rowsJ 122 123 86 400 ≤ 921559085683060 :=
  rowsJ_le_of_split 122 123 (by norm_num) (by norm_num) rows225C_714 c122_7 (by norm_num)

theorem c122_5 : rowsJ 122 123 83 400 ≤ 921559085683060 :=
  rowsJ_le_of_split 122 123 (by norm_num) (by norm_num) rows225C_713 c122_6 (by norm_num)

theorem c122_4 : rowsJ 122 123 80 400 ≤ 921559085683060 :=
  rowsJ_le_of_split 122 123 (by norm_num) (by norm_num) rows225C_712 c122_5 (by norm_num)

theorem c122_3 : rowsJ 122 123 76 400 ≤ 921559085683060 :=
  rowsJ_le_of_split 122 123 (by norm_num) (by norm_num) rows225C_711 c122_4 (by norm_num)

theorem c122_2 : rowsJ 122 123 69 400 ≤ 921559085683060 :=
  rowsJ_le_of_split 122 123 (by norm_num) (by norm_num) rows225C_710 c122_3 (by norm_num)

theorem c122_1 : rowsJ 122 123 35 400 ≤ 1198157889729904 :=
  rowsJ_le_of_split 122 123 (by norm_num) (by norm_num) rows225C_709 c122_2 (by norm_num)

theorem c122_0 : rowsJ 122 123 0 400 ≤ 1312385594172972 :=
  rowsJ_le_of_split 122 123 (by norm_num) (by norm_num) rows225C_708 c122_1 (by norm_num)

theorem hr122 : rows 122 123 ≤ 1312385594172972 := rows_le_of_rowsJ 122 123 c122_0

theorem c123_12 : rowsJ 123 124 107 400 ≤ 1001633575917380 :=
  rowsJ_le_of_split 123 124 (by norm_num) (by norm_num) rows225C_734 rows225C_735 (by norm_num)

theorem c123_11 : rowsJ 123 124 103 400 ≤ 1008863103818482 :=
  rowsJ_le_of_split 123 124 (by norm_num) (by norm_num) rows225C_733 c123_12 (by norm_num)

theorem c123_10 : rowsJ 123 124 99 400 ≤ 1011504232570829 :=
  rowsJ_le_of_split 123 124 (by norm_num) (by norm_num) rows225C_732 c123_11 (by norm_num)

theorem c123_9 : rowsJ 123 124 95 400 ≤ 1011880897610173 :=
  rowsJ_le_of_split 123 124 (by norm_num) (by norm_num) rows225C_731 c123_10 (by norm_num)

theorem c123_8 : rowsJ 123 124 92 400 ≤ 1011880897610173 :=
  rowsJ_le_of_split 123 124 (by norm_num) (by norm_num) rows225C_730 c123_9 (by norm_num)

theorem c123_7 : rowsJ 123 124 89 400 ≤ 1011880897610173 :=
  rowsJ_le_of_split 123 124 (by norm_num) (by norm_num) rows225C_729 c123_8 (by norm_num)

theorem c123_6 : rowsJ 123 124 86 400 ≤ 1011880897610173 :=
  rowsJ_le_of_split 123 124 (by norm_num) (by norm_num) rows225C_728 c123_7 (by norm_num)

theorem c123_5 : rowsJ 123 124 83 400 ≤ 1011880897610173 :=
  rowsJ_le_of_split 123 124 (by norm_num) (by norm_num) rows225C_727 c123_6 (by norm_num)

theorem c123_4 : rowsJ 123 124 80 400 ≤ 1011880897610173 :=
  rowsJ_le_of_split 123 124 (by norm_num) (by norm_num) rows225C_726 c123_5 (by norm_num)

theorem c123_3 : rowsJ 123 124 76 400 ≤ 1011880897610173 :=
  rowsJ_le_of_split 123 124 (by norm_num) (by norm_num) rows225C_725 c123_4 (by norm_num)

theorem c123_2 : rowsJ 123 124 69 400 ≤ 1011880897610173 :=
  rowsJ_le_of_split 123 124 (by norm_num) (by norm_num) rows225C_724 c123_3 (by norm_num)

theorem c123_1 : rowsJ 123 124 35 400 ≤ 1269558162039271 :=
  rowsJ_le_of_split 123 124 (by norm_num) (by norm_num) rows225C_723 c123_2 (by norm_num)

theorem c123_0 : rowsJ 123 124 0 400 ≤ 1390758890186874 :=
  rowsJ_le_of_split 123 124 (by norm_num) (by norm_num) rows225C_722 c123_1 (by norm_num)

theorem hr123 : rows 123 124 ≤ 1390758890186874 := rows_le_of_rowsJ 123 124 c123_0

theorem c124_12 : rowsJ 124 125 106 400 ≤ 1187418664417520 :=
  rowsJ_le_of_split 124 125 (by norm_num) (by norm_num) rows225C_748 rows225C_749 (by norm_num)

theorem c124_11 : rowsJ 124 125 102 400 ≤ 1193730795846348 :=
  rowsJ_le_of_split 124 125 (by norm_num) (by norm_num) rows225C_747 c124_12 (by norm_num)

theorem c124_10 : rowsJ 124 125 98 400 ≤ 1195803430507062 :=
  rowsJ_le_of_split 124 125 (by norm_num) (by norm_num) rows225C_746 c124_11 (by norm_num)

theorem c124_9 : rowsJ 124 125 94 400 ≤ 1195982606733850 :=
  rowsJ_le_of_split 124 125 (by norm_num) (by norm_num) rows225C_745 c124_10 (by norm_num)

theorem c124_8 : rowsJ 124 125 91 400 ≤ 1195982606733850 :=
  rowsJ_le_of_split 124 125 (by norm_num) (by norm_num) rows225C_744 c124_9 (by norm_num)

theorem c124_7 : rowsJ 124 125 88 400 ≤ 1195982606733850 :=
  rowsJ_le_of_split 124 125 (by norm_num) (by norm_num) rows225C_743 c124_8 (by norm_num)

theorem c124_6 : rowsJ 124 125 85 400 ≤ 1195982606733850 :=
  rowsJ_le_of_split 124 125 (by norm_num) (by norm_num) rows225C_742 c124_7 (by norm_num)

theorem c124_5 : rowsJ 124 125 82 400 ≤ 1195982606733850 :=
  rowsJ_le_of_split 124 125 (by norm_num) (by norm_num) rows225C_741 c124_6 (by norm_num)

theorem c124_4 : rowsJ 124 125 79 400 ≤ 1195982606733850 :=
  rowsJ_le_of_split 124 125 (by norm_num) (by norm_num) rows225C_740 c124_5 (by norm_num)

theorem c124_3 : rowsJ 124 125 75 400 ≤ 1195982606733850 :=
  rowsJ_le_of_split 124 125 (by norm_num) (by norm_num) rows225C_739 c124_4 (by norm_num)

theorem c124_2 : rowsJ 124 125 69 400 ≤ 1195982606733850 :=
  rowsJ_le_of_split 124 125 (by norm_num) (by norm_num) rows225C_738 c124_3 (by norm_num)

theorem c124_1 : rowsJ 124 125 35 400 ≤ 1435457083019586 :=
  rowsJ_le_of_split 124 125 (by norm_num) (by norm_num) rows225C_737 c124_2 (by norm_num)

theorem c124_0 : rowsJ 124 125 0 400 ≤ 1562365756881567 :=
  rowsJ_le_of_split 124 125 (by norm_num) (by norm_num) rows225C_736 c124_1 (by norm_num)

theorem hr124 : rows 124 125 ≤ 1562365756881567 := rows_le_of_rowsJ 124 125 c124_0

theorem c125_12 : rowsJ 125 126 107 400 ≤ 1269735917843630 :=
  rowsJ_le_of_split 125 126 (by norm_num) (by norm_num) rows225C_762 rows225C_763 (by norm_num)

theorem c125_11 : rowsJ 125 126 102 400 ≤ 1279269004311165 :=
  rowsJ_le_of_split 125 126 (by norm_num) (by norm_num) rows225C_761 c125_12 (by norm_num)

theorem c125_10 : rowsJ 125 126 98 400 ≤ 1281599235802998 :=
  rowsJ_le_of_split 125 126 (by norm_num) (by norm_num) rows225C_760 c125_11 (by norm_num)

theorem c125_9 : rowsJ 125 126 94 400 ≤ 1281825752498747 :=
  rowsJ_le_of_split 125 126 (by norm_num) (by norm_num) rows225C_759 c125_10 (by norm_num)

theorem c125_8 : rowsJ 125 126 91 400 ≤ 1281825752498747 :=
  rowsJ_le_of_split 125 126 (by norm_num) (by norm_num) rows225C_758 c125_9 (by norm_num)

theorem c125_7 : rowsJ 125 126 88 400 ≤ 1281825752498747 :=
  rowsJ_le_of_split 125 126 (by norm_num) (by norm_num) rows225C_757 c125_8 (by norm_num)

theorem c125_6 : rowsJ 125 126 85 400 ≤ 1281825752498747 :=
  rowsJ_le_of_split 125 126 (by norm_num) (by norm_num) rows225C_756 c125_7 (by norm_num)

theorem c125_5 : rowsJ 125 126 82 400 ≤ 1281825752498747 :=
  rowsJ_le_of_split 125 126 (by norm_num) (by norm_num) rows225C_755 c125_6 (by norm_num)

theorem c125_4 : rowsJ 125 126 79 400 ≤ 1281825752498747 :=
  rowsJ_le_of_split 125 126 (by norm_num) (by norm_num) rows225C_754 c125_5 (by norm_num)

theorem c125_3 : rowsJ 125 126 75 400 ≤ 1281825752498747 :=
  rowsJ_le_of_split 125 126 (by norm_num) (by norm_num) rows225C_753 c125_4 (by norm_num)

theorem c125_2 : rowsJ 125 126 69 400 ≤ 1281825752498747 :=
  rowsJ_le_of_split 125 126 (by norm_num) (by norm_num) rows225C_752 c125_3 (by norm_num)

theorem c125_1 : rowsJ 125 126 35 400 ≤ 1503858252782093 :=
  rowsJ_le_of_split 125 126 (by norm_num) (by norm_num) rows225C_751 c125_2 (by norm_num)

theorem c125_0 : rowsJ 125 126 0 400 ≤ 1636832423513079 :=
  rowsJ_le_of_split 125 126 (by norm_num) (by norm_num) rows225C_750 c125_1 (by norm_num)

theorem hr125 : rows 125 126 ≤ 1636832423513079 := rows_le_of_rowsJ 125 126 c125_0

theorem c126_11 : rowsJ 126 127 103 400 ≤ 1457647576669369 :=
  rowsJ_le_of_split 126 127 (by norm_num) (by norm_num) rows225C_775 rows225C_776 (by norm_num)

theorem c126_10 : rowsJ 126 127 99 400 ≤ 1461154418408346 :=
  rowsJ_le_of_split 126 127 (by norm_num) (by norm_num) rows225C_774 c126_11 (by norm_num)

theorem c126_9 : rowsJ 126 127 95 400 ≤ 1461731417346045 :=
  rowsJ_le_of_split 126 127 (by norm_num) (by norm_num) rows225C_773 c126_10 (by norm_num)

theorem c126_8 : rowsJ 126 127 91 400 ≤ 1461731417346045 :=
  rowsJ_le_of_split 126 127 (by norm_num) (by norm_num) rows225C_772 c126_9 (by norm_num)

theorem c126_7 : rowsJ 126 127 88 400 ≤ 1461731417346045 :=
  rowsJ_le_of_split 126 127 (by norm_num) (by norm_num) rows225C_771 c126_8 (by norm_num)

theorem c126_6 : rowsJ 126 127 85 400 ≤ 1461731417346045 :=
  rowsJ_le_of_split 126 127 (by norm_num) (by norm_num) rows225C_770 c126_7 (by norm_num)

theorem c126_5 : rowsJ 126 127 82 400 ≤ 1461731417346045 :=
  rowsJ_le_of_split 126 127 (by norm_num) (by norm_num) rows225C_769 c126_6 (by norm_num)

theorem c126_4 : rowsJ 126 127 79 400 ≤ 1461731417346045 :=
  rowsJ_le_of_split 126 127 (by norm_num) (by norm_num) rows225C_768 c126_5 (by norm_num)

theorem c126_3 : rowsJ 126 127 75 400 ≤ 1461731417346045 :=
  rowsJ_le_of_split 126 127 (by norm_num) (by norm_num) rows225C_767 c126_4 (by norm_num)

theorem c126_2 : rowsJ 126 127 70 400 ≤ 1461731417346045 :=
  rowsJ_le_of_split 126 127 (by norm_num) (by norm_num) rows225C_766 c126_3 (by norm_num)

theorem c126_1 : rowsJ 126 127 36 400 ≤ 1650280631452573 :=
  rowsJ_le_of_split 126 127 (by norm_num) (by norm_num) rows225C_765 c126_2 (by norm_num)

theorem c126_0 : rowsJ 126 127 0 400 ≤ 1804892281493043 :=
  rowsJ_le_of_split 126 127 (by norm_num) (by norm_num) rows225C_764 c126_1 (by norm_num)

theorem hr126 : rows 126 127 ≤ 1804892281493043 := rows_le_of_rowsJ 126 127 c126_0

theorem c127_11 : rowsJ 127 128 103 400 ≤ 1452076616872939 :=
  rowsJ_le_of_split 127 128 (by norm_num) (by norm_num) rows225C_788 rows225C_789 (by norm_num)

theorem c127_10 : rowsJ 127 128 99 400 ≤ 1455917690126516 :=
  rowsJ_le_of_split 127 128 (by norm_num) (by norm_num) rows225C_787 c127_11 (by norm_num)

theorem c127_9 : rowsJ 127 128 95 400 ≤ 1456595302674144 :=
  rowsJ_le_of_split 127 128 (by norm_num) (by norm_num) rows225C_786 c127_10 (by norm_num)

theorem c127_8 : rowsJ 127 128 91 400 ≤ 1456595302674144 :=
  rowsJ_le_of_split 127 128 (by norm_num) (by norm_num) rows225C_785 c127_9 (by norm_num)

theorem c127_7 : rowsJ 127 128 88 400 ≤ 1456595302674144 :=
  rowsJ_le_of_split 127 128 (by norm_num) (by norm_num) rows225C_784 c127_8 (by norm_num)

theorem c127_6 : rowsJ 127 128 85 400 ≤ 1456595302674144 :=
  rowsJ_le_of_split 127 128 (by norm_num) (by norm_num) rows225C_783 c127_7 (by norm_num)

theorem c127_5 : rowsJ 127 128 82 400 ≤ 1456595302674144 :=
  rowsJ_le_of_split 127 128 (by norm_num) (by norm_num) rows225C_782 c127_6 (by norm_num)

theorem c127_4 : rowsJ 127 128 79 400 ≤ 1456595302674144 :=
  rowsJ_le_of_split 127 128 (by norm_num) (by norm_num) rows225C_781 c127_5 (by norm_num)

theorem c127_3 : rowsJ 127 128 75 400 ≤ 1456595302674144 :=
  rowsJ_le_of_split 127 128 (by norm_num) (by norm_num) rows225C_780 c127_4 (by norm_num)

theorem c127_2 : rowsJ 127 128 70 400 ≤ 1456595302674144 :=
  rowsJ_le_of_split 127 128 (by norm_num) (by norm_num) rows225C_779 c127_3 (by norm_num)

theorem c127_1 : rowsJ 127 128 36 400 ≤ 1630016505081871 :=
  rowsJ_le_of_split 127 128 (by norm_num) (by norm_num) rows225C_778 c127_2 (by norm_num)

theorem c127_0 : rowsJ 127 128 0 400 ≤ 1789072027797637 :=
  rowsJ_le_of_split 127 128 (by norm_num) (by norm_num) rows225C_777 c127_1 (by norm_num)

theorem hr127 : rows 127 128 ≤ 1789072027797637 := rows_le_of_rowsJ 127 128 c127_0

theorem c128_11 : rowsJ 128 129 104 400 ≤ 1453766660855090 :=
  rowsJ_le_of_split 128 129 (by norm_num) (by norm_num) rows225C_801 rows225C_802 (by norm_num)

theorem c128_10 : rowsJ 128 129 99 400 ≤ 1459772533523979 :=
  rowsJ_le_of_split 128 129 (by norm_num) (by norm_num) rows225C_800 c128_11 (by norm_num)

theorem c128_9 : rowsJ 128 129 95 400 ≤ 1460507727083850 :=
  rowsJ_le_of_split 128 129 (by norm_num) (by norm_num) rows225C_799 c128_10 (by norm_num)

theorem c128_8 : rowsJ 128 129 91 400 ≤ 1460507727083850 :=
  rowsJ_le_of_split 128 129 (by norm_num) (by norm_num) rows225C_798 c128_9 (by norm_num)

theorem c128_7 : rowsJ 128 129 88 400 ≤ 1460507727083850 :=
  rowsJ_le_of_split 128 129 (by norm_num) (by norm_num) rows225C_797 c128_8 (by norm_num)

theorem c128_6 : rowsJ 128 129 85 400 ≤ 1460507727083850 :=
  rowsJ_le_of_split 128 129 (by norm_num) (by norm_num) rows225C_796 c128_7 (by norm_num)

theorem c128_5 : rowsJ 128 129 82 400 ≤ 1460507727083850 :=
  rowsJ_le_of_split 128 129 (by norm_num) (by norm_num) rows225C_795 c128_6 (by norm_num)

theorem c128_4 : rowsJ 128 129 79 400 ≤ 1460507727083850 :=
  rowsJ_le_of_split 128 129 (by norm_num) (by norm_num) rows225C_794 c128_5 (by norm_num)

theorem c128_3 : rowsJ 128 129 75 400 ≤ 1460507727083850 :=
  rowsJ_le_of_split 128 129 (by norm_num) (by norm_num) rows225C_793 c128_4 (by norm_num)

theorem c128_2 : rowsJ 128 129 70 400 ≤ 1460507727083850 :=
  rowsJ_le_of_split 128 129 (by norm_num) (by norm_num) rows225C_792 c128_3 (by norm_num)

theorem c128_1 : rowsJ 128 129 37 400 ≤ 1605162297894433 :=
  rowsJ_le_of_split 128 129 (by norm_num) (by norm_num) rows225C_791 c128_2 (by norm_num)

theorem c128_0 : rowsJ 128 129 0 400 ≤ 1781668183969174 :=
  rowsJ_le_of_split 128 129 (by norm_num) (by norm_num) rows225C_790 c128_1 (by norm_num)

theorem hr128 : rows 128 129 ≤ 1781668183969174 := rows_le_of_rowsJ 128 129 c128_0

theorem c129_10 : rowsJ 129 130 100 400 ≤ 1366142200199690 :=
  rowsJ_le_of_split 129 130 (by norm_num) (by norm_num) rows225C_813 rows225C_814 (by norm_num)

theorem c129_9 : rowsJ 129 130 96 400 ≤ 1367662188887195 :=
  rowsJ_le_of_split 129 130 (by norm_num) (by norm_num) rows225C_812 c129_10 (by norm_num)

theorem c129_8 : rowsJ 129 130 92 400 ≤ 1367662188887195 :=
  rowsJ_le_of_split 129 130 (by norm_num) (by norm_num) rows225C_811 c129_9 (by norm_num)

theorem c129_7 : rowsJ 129 130 88 400 ≤ 1367662188887195 :=
  rowsJ_le_of_split 129 130 (by norm_num) (by norm_num) rows225C_810 c129_8 (by norm_num)

theorem c129_6 : rowsJ 129 130 85 400 ≤ 1367662188887195 :=
  rowsJ_le_of_split 129 130 (by norm_num) (by norm_num) rows225C_809 c129_7 (by norm_num)

theorem c129_5 : rowsJ 129 130 82 400 ≤ 1367662188887195 :=
  rowsJ_le_of_split 129 130 (by norm_num) (by norm_num) rows225C_808 c129_6 (by norm_num)

theorem c129_4 : rowsJ 129 130 79 400 ≤ 1367662188887195 :=
  rowsJ_le_of_split 129 130 (by norm_num) (by norm_num) rows225C_807 c129_5 (by norm_num)

theorem c129_3 : rowsJ 129 130 75 400 ≤ 1367662188887195 :=
  rowsJ_le_of_split 129 130 (by norm_num) (by norm_num) rows225C_806 c129_4 (by norm_num)

theorem c129_2 : rowsJ 129 130 70 400 ≤ 1367662188887195 :=
  rowsJ_le_of_split 129 130 (by norm_num) (by norm_num) rows225C_805 c129_3 (by norm_num)

theorem c129_1 : rowsJ 129 130 37 400 ≤ 1499596371194270 :=
  rowsJ_le_of_split 129 130 (by norm_num) (by norm_num) rows225C_804 c129_2 (by norm_num)

theorem c129_0 : rowsJ 129 130 0 400 ≤ 1678775900662844 :=
  rowsJ_le_of_split 129 130 (by norm_num) (by norm_num) rows225C_803 c129_1 (by norm_num)

theorem hr129 : rows 129 130 ≤ 1678775900662844 := rows_le_of_rowsJ 129 130 c129_0

theorem c130_10 : rowsJ 130 131 99 400 ≤ 1370337612072874 :=
  rowsJ_le_of_split 130 131 (by norm_num) (by norm_num) rows225C_825 rows225C_826 (by norm_num)

theorem c130_9 : rowsJ 130 131 95 400 ≤ 1371239926400833 :=
  rowsJ_le_of_split 130 131 (by norm_num) (by norm_num) rows225C_824 c130_10 (by norm_num)

theorem c130_8 : rowsJ 130 131 91 400 ≤ 1371239926400833 :=
  rowsJ_le_of_split 130 131 (by norm_num) (by norm_num) rows225C_823 c130_9 (by norm_num)

theorem c130_7 : rowsJ 130 131 87 400 ≤ 1371239926400833 :=
  rowsJ_le_of_split 130 131 (by norm_num) (by norm_num) rows225C_822 c130_8 (by norm_num)

theorem c130_6 : rowsJ 130 131 84 400 ≤ 1371239926400833 :=
  rowsJ_le_of_split 130 131 (by norm_num) (by norm_num) rows225C_821 c130_7 (by norm_num)

theorem c130_5 : rowsJ 130 131 81 400 ≤ 1371239926400833 :=
  rowsJ_le_of_split 130 131 (by norm_num) (by norm_num) rows225C_820 c130_6 (by norm_num)

theorem c130_4 : rowsJ 130 131 78 400 ≤ 1371239926400833 :=
  rowsJ_le_of_split 130 131 (by norm_num) (by norm_num) rows225C_819 c130_5 (by norm_num)

theorem c130_3 : rowsJ 130 131 75 400 ≤ 1371239926400833 :=
  rowsJ_le_of_split 130 131 (by norm_num) (by norm_num) rows225C_818 c130_4 (by norm_num)

theorem c130_2 : rowsJ 130 131 70 400 ≤ 1371239926400833 :=
  rowsJ_le_of_split 130 131 (by norm_num) (by norm_num) rows225C_817 c130_3 (by norm_num)

theorem c130_1 : rowsJ 130 131 38 400 ≤ 1479093228872171 :=
  rowsJ_le_of_split 130 131 (by norm_num) (by norm_num) rows225C_816 c130_2 (by norm_num)

theorem c130_0 : rowsJ 130 131 0 400 ≤ 1671700875914603 :=
  rowsJ_le_of_split 130 131 (by norm_num) (by norm_num) rows225C_815 c130_1 (by norm_num)

theorem hr130 : rows 130 131 ≤ 1671700875914603 := rows_le_of_rowsJ 130 131 c130_0

theorem c131_10 : rowsJ 131 132 99 400 ≤ 1276747780969843 :=
  rowsJ_le_of_split 131 132 (by norm_num) (by norm_num) rows225C_837 rows225C_838 (by norm_num)

theorem c131_9 : rowsJ 131 132 95 400 ≤ 1277760807538250 :=
  rowsJ_le_of_split 131 132 (by norm_num) (by norm_num) rows225C_836 c131_10 (by norm_num)

theorem c131_8 : rowsJ 131 132 91 400 ≤ 1277760807538250 :=
  rowsJ_le_of_split 131 132 (by norm_num) (by norm_num) rows225C_835 c131_9 (by norm_num)

theorem c131_7 : rowsJ 131 132 87 400 ≤ 1277760807538250 :=
  rowsJ_le_of_split 131 132 (by norm_num) (by norm_num) rows225C_834 c131_8 (by norm_num)

theorem c131_6 : rowsJ 131 132 84 400 ≤ 1277760807538250 :=
  rowsJ_le_of_split 131 132 (by norm_num) (by norm_num) rows225C_833 c131_7 (by norm_num)

theorem c131_5 : rowsJ 131 132 81 400 ≤ 1277760807538250 :=
  rowsJ_le_of_split 131 132 (by norm_num) (by norm_num) rows225C_832 c131_6 (by norm_num)

theorem c131_4 : rowsJ 131 132 78 400 ≤ 1277760807538250 :=
  rowsJ_le_of_split 131 132 (by norm_num) (by norm_num) rows225C_831 c131_5 (by norm_num)

theorem c131_3 : rowsJ 131 132 75 400 ≤ 1277760807538250 :=
  rowsJ_le_of_split 131 132 (by norm_num) (by norm_num) rows225C_830 c131_4 (by norm_num)

theorem c131_2 : rowsJ 131 132 70 400 ≤ 1277760807538250 :=
  rowsJ_le_of_split 131 132 (by norm_num) (by norm_num) rows225C_829 c131_3 (by norm_num)

theorem c131_1 : rowsJ 131 132 39 400 ≤ 1364658328119800 :=
  rowsJ_le_of_split 131 132 (by norm_num) (by norm_num) rows225C_828 c131_2 (by norm_num)

theorem c131_0 : rowsJ 131 132 0 400 ≤ 1568884844197055 :=
  rowsJ_le_of_split 131 132 (by norm_num) (by norm_num) rows225C_827 c131_1 (by norm_num)

theorem hr131 : rows 131 132 ≤ 1568884844197055 := rows_le_of_rowsJ 131 132 c131_0

theorem c132_10 : rowsJ 132 133 100 400 ≤ 1279057571188318 :=
  rowsJ_le_of_split 132 133 (by norm_num) (by norm_num) rows225C_849 rows225C_850 (by norm_num)

theorem c132_9 : rowsJ 132 133 95 400 ≤ 1280998697424448 :=
  rowsJ_le_of_split 132 133 (by norm_num) (by norm_num) rows225C_848 c132_10 (by norm_num)

theorem c132_8 : rowsJ 132 133 91 400 ≤ 1280998697424448 :=
  rowsJ_le_of_split 132 133 (by norm_num) (by norm_num) rows225C_847 c132_9 (by norm_num)

theorem c132_7 : rowsJ 132 133 87 400 ≤ 1280998697424448 :=
  rowsJ_le_of_split 132 133 (by norm_num) (by norm_num) rows225C_846 c132_8 (by norm_num)

theorem c132_6 : rowsJ 132 133 84 400 ≤ 1280998697424448 :=
  rowsJ_le_of_split 132 133 (by norm_num) (by norm_num) rows225C_845 c132_7 (by norm_num)

theorem c132_5 : rowsJ 132 133 81 400 ≤ 1280998697424448 :=
  rowsJ_le_of_split 132 133 (by norm_num) (by norm_num) rows225C_844 c132_6 (by norm_num)

theorem c132_4 : rowsJ 132 133 78 400 ≤ 1280998697424448 :=
  rowsJ_le_of_split 132 133 (by norm_num) (by norm_num) rows225C_843 c132_5 (by norm_num)

theorem c132_3 : rowsJ 132 133 75 400 ≤ 1280998697424448 :=
  rowsJ_le_of_split 132 133 (by norm_num) (by norm_num) rows225C_842 c132_4 (by norm_num)

theorem c132_2 : rowsJ 132 133 70 400 ≤ 1281138446268868 :=
  rowsJ_le_of_split 132 133 (by norm_num) (by norm_num) rows225C_841 c132_3 (by norm_num)

theorem c132_1 : rowsJ 132 133 40 400 ≤ 1349874830821688 :=
  rowsJ_le_of_split 132 133 (by norm_num) (by norm_num) rows225C_840 c132_2 (by norm_num)

theorem c132_0 : rowsJ 132 133 0 400 ≤ 1562274022967235 :=
  rowsJ_le_of_split 132 133 (by norm_num) (by norm_num) rows225C_839 c132_1 (by norm_num)

theorem hr132 : rows 132 133 ≤ 1562274022967235 := rows_le_of_rowsJ 132 133 c132_0

theorem c133_10 : rowsJ 133 134 99 400 ≤ 1185658199763581 :=
  rowsJ_le_of_split 133 134 (by norm_num) (by norm_num) rows225C_861 rows225C_862 (by norm_num)

theorem c133_9 : rowsJ 133 134 94 400 ≤ 1186853668382880 :=
  rowsJ_le_of_split 133 134 (by norm_num) (by norm_num) rows225C_860 c133_10 (by norm_num)

theorem c133_8 : rowsJ 133 134 90 400 ≤ 1186853668382880 :=
  rowsJ_le_of_split 133 134 (by norm_num) (by norm_num) rows225C_859 c133_9 (by norm_num)

theorem c133_7 : rowsJ 133 134 86 400 ≤ 1186853668382880 :=
  rowsJ_le_of_split 133 134 (by norm_num) (by norm_num) rows225C_858 c133_8 (by norm_num)

theorem c133_6 : rowsJ 133 134 83 400 ≤ 1186853668382880 :=
  rowsJ_le_of_split 133 134 (by norm_num) (by norm_num) rows225C_857 c133_7 (by norm_num)

theorem c133_5 : rowsJ 133 134 80 400 ≤ 1186853668382880 :=
  rowsJ_le_of_split 133 134 (by norm_num) (by norm_num) rows225C_856 c133_6 (by norm_num)

theorem c133_4 : rowsJ 133 134 77 400 ≤ 1186853668382880 :=
  rowsJ_le_of_split 133 134 (by norm_num) (by norm_num) rows225C_855 c133_5 (by norm_num)

theorem c133_3 : rowsJ 133 134 74 400 ≤ 1186853668382880 :=
  rowsJ_le_of_split 133 134 (by norm_num) (by norm_num) rows225C_854 c133_4 (by norm_num)

theorem c133_2 : rowsJ 133 134 70 400 ≤ 1187312316072898 :=
  rowsJ_le_of_split 133 134 (by norm_num) (by norm_num) rows225C_853 c133_3 (by norm_num)

theorem c133_1 : rowsJ 133 134 43 400 ≤ 1226975397249712 :=
  rowsJ_le_of_split 133 134 (by norm_num) (by norm_num) rows225C_852 c133_2 (by norm_num)

theorem c133_0 : rowsJ 133 134 0 400 ≤ 1459644564173197 :=
  rowsJ_le_of_split 133 134 (by norm_num) (by norm_num) rows225C_851 c133_1 (by norm_num)

theorem hr133 : rows 133 134 ≤ 1459644564173197 := rows_le_of_rowsJ 133 134 c133_0

theorem c134_10 : rowsJ 134 135 100 400 ≤ 1187488842737659 :=
  rowsJ_le_of_split 134 135 (by norm_num) (by norm_num) rows225C_873 rows225C_874 (by norm_num)

theorem c134_9 : rowsJ 134 135 95 400 ≤ 1189747918541326 :=
  rowsJ_le_of_split 134 135 (by norm_num) (by norm_num) rows225C_872 c134_10 (by norm_num)

theorem c134_8 : rowsJ 134 135 91 400 ≤ 1189747918541326 :=
  rowsJ_le_of_split 134 135 (by norm_num) (by norm_num) rows225C_871 c134_9 (by norm_num)

theorem c134_7 : rowsJ 134 135 87 400 ≤ 1189747918541326 :=
  rowsJ_le_of_split 134 135 (by norm_num) (by norm_num) rows225C_870 c134_8 (by norm_num)

theorem c134_6 : rowsJ 134 135 83 400 ≤ 1189747918541326 :=
  rowsJ_le_of_split 134 135 (by norm_num) (by norm_num) rows225C_869 c134_7 (by norm_num)

theorem c134_5 : rowsJ 134 135 80 400 ≤ 1189747918541326 :=
  rowsJ_le_of_split 134 135 (by norm_num) (by norm_num) rows225C_868 c134_6 (by norm_num)

theorem c134_4 : rowsJ 134 135 77 400 ≤ 1189747918541326 :=
  rowsJ_le_of_split 134 135 (by norm_num) (by norm_num) rows225C_867 c134_5 (by norm_num)

theorem c134_3 : rowsJ 134 135 74 400 ≤ 1189747918541326 :=
  rowsJ_le_of_split 134 135 (by norm_num) (by norm_num) rows225C_866 c134_4 (by norm_num)

theorem c134_2 : rowsJ 134 135 70 400 ≤ 1190708272773074 :=
  rowsJ_le_of_split 134 135 (by norm_num) (by norm_num) rows225C_865 c134_3 (by norm_num)

theorem c134_1 : rowsJ 134 135 48 400 ≤ 1204526375857698 :=
  rowsJ_le_of_split 134 135 (by norm_num) (by norm_num) rows225C_864 c134_2 (by norm_num)

theorem c134_0 : rowsJ 134 135 0 400 ≤ 1453573848034954 :=
  rowsJ_le_of_split 134 135 (by norm_num) (by norm_num) rows225C_863 c134_1 (by norm_num)

theorem hr134 : rows 134 135 ≤ 1453573848034954 := rows_le_of_rowsJ 134 135 c134_0

theorem c135_10 : rowsJ 135 136 100 400 ≤ 1092427382132311 :=
  rowsJ_le_of_split 135 136 (by norm_num) (by norm_num) rows225C_885 rows225C_886 (by norm_num)

theorem c135_9 : rowsJ 135 136 95 400 ≤ 1094876848792225 :=
  rowsJ_le_of_split 135 136 (by norm_num) (by norm_num) rows225C_884 c135_10 (by norm_num)

theorem c135_8 : rowsJ 135 136 91 400 ≤ 1094876848792225 :=
  rowsJ_le_of_split 135 136 (by norm_num) (by norm_num) rows225C_883 c135_9 (by norm_num)

theorem c135_7 : rowsJ 135 136 87 400 ≤ 1094876848792225 :=
  rowsJ_le_of_split 135 136 (by norm_num) (by norm_num) rows225C_882 c135_8 (by norm_num)

theorem c135_6 : rowsJ 135 136 83 400 ≤ 1094876848792225 :=
  rowsJ_le_of_split 135 136 (by norm_num) (by norm_num) rows225C_881 c135_7 (by norm_num)

theorem c135_5 : rowsJ 135 136 80 400 ≤ 1094876848792225 :=
  rowsJ_le_of_split 135 136 (by norm_num) (by norm_num) rows225C_880 c135_6 (by norm_num)

theorem c135_4 : rowsJ 135 136 77 400 ≤ 1094876848792225 :=
  rowsJ_le_of_split 135 136 (by norm_num) (by norm_num) rows225C_879 c135_5 (by norm_num)

theorem c135_3 : rowsJ 135 136 74 400 ≤ 1094876848792225 :=
  rowsJ_le_of_split 135 136 (by norm_num) (by norm_num) rows225C_878 c135_4 (by norm_num)

theorem c135_2 : rowsJ 135 136 69 400 ≤ 1097274781416499 :=
  rowsJ_le_of_split 135 136 (by norm_num) (by norm_num) rows225C_877 c135_3 (by norm_num)

theorem c135_1 : rowsJ 135 136 60 400 ≤ 1101770457322664 :=
  rowsJ_le_of_split 135 136 (by norm_num) (by norm_num) rows225C_876 c135_2 (by norm_num)

theorem c135_0 : rowsJ 135 136 0 400 ≤ 1351221408956725 :=
  rowsJ_le_of_split 135 136 (by norm_num) (by norm_num) rows225C_875 c135_1 (by norm_num)

theorem hr135 : rows 135 136 ≤ 1351221408956725 := rows_le_of_rowsJ 135 136 c135_0

theorem c136_10 : rowsJ 136 137 99 400 ≤ 1095960195725164 :=
  rowsJ_le_of_split 136 137 (by norm_num) (by norm_num) rows225C_897 rows225C_898 (by norm_num)

theorem c136_9 : rowsJ 136 137 94 400 ≤ 1097425176674058 :=
  rowsJ_le_of_split 136 137 (by norm_num) (by norm_num) rows225C_896 c136_10 (by norm_num)

theorem c136_8 : rowsJ 136 137 90 400 ≤ 1097425176674058 :=
  rowsJ_le_of_split 136 137 (by norm_num) (by norm_num) rows225C_895 c136_9 (by norm_num)

theorem c136_7 : rowsJ 136 137 86 400 ≤ 1097425176674058 :=
  rowsJ_le_of_split 136 137 (by norm_num) (by norm_num) rows225C_894 c136_8 (by norm_num)

theorem c136_6 : rowsJ 136 137 82 400 ≤ 1097425176674058 :=
  rowsJ_le_of_split 136 137 (by norm_num) (by norm_num) rows225C_893 c136_7 (by norm_num)

theorem c136_5 : rowsJ 136 137 79 400 ≤ 1097425176674058 :=
  rowsJ_le_of_split 136 137 (by norm_num) (by norm_num) rows225C_892 c136_6 (by norm_num)

theorem c136_4 : rowsJ 136 137 76 400 ≤ 1097425176674058 :=
  rowsJ_le_of_split 136 137 (by norm_num) (by norm_num) rows225C_891 c136_5 (by norm_num)

theorem c136_3 : rowsJ 136 137 73 400 ≤ 1098064690667305 :=
  rowsJ_le_of_split 136 137 (by norm_num) (by norm_num) rows225C_890 c136_4 (by norm_num)

theorem c136_2 : rowsJ 136 137 69 400 ≤ 1100957017143112 :=
  rowsJ_le_of_split 136 137 (by norm_num) (by norm_num) rows225C_889 c136_3 (by norm_num)

theorem c136_1 : rowsJ 136 137 60 400 ≤ 1106274644598381 :=
  rowsJ_le_of_split 136 137 (by norm_num) (by norm_num) rows225C_888 c136_2 (by norm_num)

theorem c136_0 : rowsJ 136 137 0 400 ≤ 1345841936799508 :=
  rowsJ_le_of_split 136 137 (by norm_num) (by norm_num) rows225C_887 c136_1 (by norm_num)

theorem hr136 : rows 136 137 ≤ 1345841936799508 := rows_le_of_rowsJ 136 137 c136_0

theorem c137_10 : rowsJ 137 138 100 400 ≤ 998998099254802 :=
  rowsJ_le_of_split 137 138 (by norm_num) (by norm_num) rows225C_909 rows225C_910 (by norm_num)

theorem c137_9 : rowsJ 137 138 95 400 ≤ 1001795806447822 :=
  rowsJ_le_of_split 137 138 (by norm_num) (by norm_num) rows225C_908 c137_10 (by norm_num)

theorem c137_8 : rowsJ 137 138 90 400 ≤ 1001795806447822 :=
  rowsJ_le_of_split 137 138 (by norm_num) (by norm_num) rows225C_907 c137_9 (by norm_num)

theorem c137_7 : rowsJ 137 138 86 400 ≤ 1001795806447822 :=
  rowsJ_le_of_split 137 138 (by norm_num) (by norm_num) rows225C_906 c137_8 (by norm_num)

theorem c137_6 : rowsJ 137 138 82 400 ≤ 1001795806447822 :=
  rowsJ_le_of_split 137 138 (by norm_num) (by norm_num) rows225C_905 c137_7 (by norm_num)

theorem c137_5 : rowsJ 137 138 79 400 ≤ 1001795806447822 :=
  rowsJ_le_of_split 137 138 (by norm_num) (by norm_num) rows225C_904 c137_6 (by norm_num)

theorem c137_4 : rowsJ 137 138 76 400 ≤ 1001795806447822 :=
  rowsJ_le_of_split 137 138 (by norm_num) (by norm_num) rows225C_903 c137_5 (by norm_num)

theorem c137_3 : rowsJ 137 138 73 400 ≤ 1003145914245442 :=
  rowsJ_le_of_split 137 138 (by norm_num) (by norm_num) rows225C_902 c137_4 (by norm_num)

theorem c137_2 : rowsJ 137 138 69 400 ≤ 1006795698922489 :=
  rowsJ_le_of_split 137 138 (by norm_num) (by norm_num) rows225C_901 c137_3 (by norm_num)

theorem c137_1 : rowsJ 137 138 61 400 ≤ 1012846561146893 :=
  rowsJ_le_of_split 137 138 (by norm_num) (by norm_num) rows225C_900 c137_2 (by norm_num)

theorem c137_0 : rowsJ 137 138 0 400 ≤ 1243823120304461 :=
  rowsJ_le_of_split 137 138 (by norm_num) (by norm_num) rows225C_899 c137_1 (by norm_num)

theorem hr137 : rows 137 138 ≤ 1243823120304461 := rows_le_of_rowsJ 137 138 c137_0

theorem c138_9 : rowsJ 138 139 96 400 ≤ 1003997642990373 :=
  rowsJ_le_of_split 138 139 (by norm_num) (by norm_num) rows225C_920 rows225C_921 (by norm_num)

theorem c138_8 : rowsJ 138 139 91 400 ≤ 1003997642990373 :=
  rowsJ_le_of_split 138 139 (by norm_num) (by norm_num) rows225C_919 c138_9 (by norm_num)

theorem c138_7 : rowsJ 138 139 87 400 ≤ 1003997642990373 :=
  rowsJ_le_of_split 138 139 (by norm_num) (by norm_num) rows225C_918 c138_8 (by norm_num)

theorem c138_6 : rowsJ 138 139 83 400 ≤ 1003997642990373 :=
  rowsJ_le_of_split 138 139 (by norm_num) (by norm_num) rows225C_917 c138_7 (by norm_num)

theorem c138_5 : rowsJ 138 139 79 400 ≤ 1003997642990373 :=
  rowsJ_le_of_split 138 139 (by norm_num) (by norm_num) rows225C_916 c138_6 (by norm_num)

theorem c138_4 : rowsJ 138 139 76 400 ≤ 1004235230222995 :=
  rowsJ_le_of_split 138 139 (by norm_num) (by norm_num) rows225C_915 c138_5 (by norm_num)

theorem c138_3 : rowsJ 138 139 73 400 ≤ 1006301720711720 :=
  rowsJ_le_of_split 138 139 (by norm_num) (by norm_num) rows225C_914 c138_4 (by norm_num)

theorem c138_2 : rowsJ 138 139 69 400 ≤ 1010715096472663 :=
  rowsJ_le_of_split 138 139 (by norm_num) (by norm_num) rows225C_913 c138_3 (by norm_num)

theorem c138_1 : rowsJ 138 139 61 400 ≤ 1017665257781408 :=
  rowsJ_le_of_split 138 139 (by norm_num) (by norm_num) rows225C_912 c138_2 (by norm_num)

theorem c138_0 : rowsJ 138 139 0 400 ≤ 1239267855679973 :=
  rowsJ_le_of_split 138 139 (by norm_num) (by norm_num) rows225C_911 c138_1 (by norm_num)

theorem hr138 : rows 138 139 ≤ 1239267855679973 := rows_le_of_rowsJ 138 139 c138_0

theorem c139_9 : rowsJ 139 140 95 400 ≤ 907549238302162 :=
  rowsJ_le_of_split 139 140 (by norm_num) (by norm_num) rows225C_931 rows225C_932 (by norm_num)

theorem c139_8 : rowsJ 139 140 90 400 ≤ 907549238302162 :=
  rowsJ_le_of_split 139 140 (by norm_num) (by norm_num) rows225C_930 c139_9 (by norm_num)

theorem c139_7 : rowsJ 139 140 86 400 ≤ 907549238302162 :=
  rowsJ_le_of_split 139 140 (by norm_num) (by norm_num) rows225C_929 c139_8 (by norm_num)

theorem c139_6 : rowsJ 139 140 82 400 ≤ 907549238302162 :=
  rowsJ_le_of_split 139 140 (by norm_num) (by norm_num) rows225C_928 c139_7 (by norm_num)

theorem c139_5 : rowsJ 139 140 78 400 ≤ 907549238302162 :=
  rowsJ_le_of_split 139 140 (by norm_num) (by norm_num) rows225C_927 c139_6 (by norm_num)

theorem c139_4 : rowsJ 139 140 75 400 ≤ 908958460728371 :=
  rowsJ_le_of_split 139 140 (by norm_num) (by norm_num) rows225C_926 c139_5 (by norm_num)

theorem c139_3 : rowsJ 139 140 72 400 ≤ 912229932018544 :=
  rowsJ_le_of_split 139 140 (by norm_num) (by norm_num) rows225C_925 c139_4 (by norm_num)

theorem c139_2 : rowsJ 139 140 68 400 ≤ 917599863121107 :=
  rowsJ_le_of_split 139 140 (by norm_num) (by norm_num) rows225C_924 c139_3 (by norm_num)

theorem c139_1 : rowsJ 139 140 61 400 ≤ 924210848354381 :=
  rowsJ_le_of_split 139 140 (by norm_num) (by norm_num) rows225C_923 c139_2 (by norm_num)

theorem c139_0 : rowsJ 139 140 0 400 ≤ 1137511957462733 :=
  rowsJ_le_of_split 139 140 (by norm_num) (by norm_num) rows225C_922 c139_1 (by norm_num)

theorem hr139 : rows 139 140 ≤ 1137511957462733 := rows_le_of_rowsJ 139 140 c139_0

theorem c140_9 : rowsJ 140 141 95 400 ≤ 909405914253245 :=
  rowsJ_le_of_split 140 141 (by norm_num) (by norm_num) rows225C_942 rows225C_943 (by norm_num)

theorem c140_8 : rowsJ 140 141 90 400 ≤ 909405914253245 :=
  rowsJ_le_of_split 140 141 (by norm_num) (by norm_num) rows225C_941 c140_9 (by norm_num)

theorem c140_7 : rowsJ 140 141 86 400 ≤ 909405914253245 :=
  rowsJ_le_of_split 140 141 (by norm_num) (by norm_num) rows225C_940 c140_8 (by norm_num)

theorem c140_6 : rowsJ 140 141 82 400 ≤ 909405914253245 :=
  rowsJ_le_of_split 140 141 (by norm_num) (by norm_num) rows225C_939 c140_7 (by norm_num)

theorem c140_5 : rowsJ 140 141 78 400 ≤ 909600988746659 :=
  rowsJ_le_of_split 140 141 (by norm_num) (by norm_num) rows225C_938 c140_6 (by norm_num)

theorem c140_4 : rowsJ 140 141 75 400 ≤ 911597946067789 :=
  rowsJ_le_of_split 140 141 (by norm_num) (by norm_num) rows225C_937 c140_5 (by norm_num)

theorem c140_3 : rowsJ 140 141 72 400 ≤ 915593419239871 :=
  rowsJ_le_of_split 140 141 (by norm_num) (by norm_num) rows225C_936 c140_4 (by norm_num)

theorem c140_2 : rowsJ 140 141 68 400 ≤ 921737018570050 :=
  rowsJ_le_of_split 140 141 (by norm_num) (by norm_num) rows225C_935 c140_3 (by norm_num)

theorem c140_1 : rowsJ 140 141 61 400 ≤ 929195844656137 :=
  rowsJ_le_of_split 140 141 (by norm_num) (by norm_num) rows225C_934 c140_2 (by norm_num)

theorem c140_0 : rowsJ 140 141 0 400 ≤ 1133559303410202 :=
  rowsJ_le_of_split 140 141 (by norm_num) (by norm_num) rows225C_933 c140_1 (by norm_num)

theorem hr140 : rows 140 141 ≤ 1133559303410202 := rows_le_of_rowsJ 140 141 c140_0

theorem c141_9 : rowsJ 141 142 96 400 ≤ 812106465342431 :=
  rowsJ_le_of_split 141 142 (by norm_num) (by norm_num) rows225C_953 rows225C_954 (by norm_num)

theorem c141_8 : rowsJ 141 142 91 400 ≤ 812106465342431 :=
  rowsJ_le_of_split 141 142 (by norm_num) (by norm_num) rows225C_952 c141_9 (by norm_num)

theorem c141_7 : rowsJ 141 142 86 400 ≤ 812106465342431 :=
  rowsJ_le_of_split 141 142 (by norm_num) (by norm_num) rows225C_951 c141_8 (by norm_num)

theorem c141_6 : rowsJ 141 142 82 400 ≤ 812106465342431 :=
  rowsJ_le_of_split 141 142 (by norm_num) (by norm_num) rows225C_950 c141_7 (by norm_num)

theorem c141_5 : rowsJ 141 142 78 400 ≤ 812662720519137 :=
  rowsJ_le_of_split 141 142 (by norm_num) (by norm_num) rows225C_949 c141_6 (by norm_num)

theorem c141_4 : rowsJ 141 142 75 400 ≤ 815204673376742 :=
  rowsJ_le_of_split 141 142 (by norm_num) (by norm_num) rows225C_948 c141_5 (by norm_num)

theorem c141_3 : rowsJ 141 142 72 400 ≤ 819881003058350 :=
  rowsJ_le_of_split 141 142 (by norm_num) (by norm_num) rows225C_947 c141_4 (by norm_num)

theorem c141_2 : rowsJ 141 142 68 400 ≤ 826857012239914 :=
  rowsJ_le_of_split 141 142 (by norm_num) (by norm_num) rows225C_946 c141_3 (by norm_num)

theorem c141_1 : rowsJ 141 142 61 400 ≤ 835265589817365 :=
  rowsJ_le_of_split 141 142 (by norm_num) (by norm_num) rows225C_945 c141_2 (by norm_num)

theorem c141_0 : rowsJ 141 142 0 400 ≤ 1031815413734050 :=
  rowsJ_le_of_split 141 142 (by norm_num) (by norm_num) rows225C_944 c141_1 (by norm_num)

theorem hr141 : rows 141 142 ≤ 1031815413734050 := rows_le_of_rowsJ 141 142 c141_0

theorem c142_8 : rowsJ 142 143 92 400 ≤ 813621478285463 :=
  rowsJ_le_of_split 142 143 (by norm_num) (by norm_num) rows225C_963 rows225C_964 (by norm_num)

theorem c142_7 : rowsJ 142 143 87 400 ≤ 813621478285463 :=
  rowsJ_le_of_split 142 143 (by norm_num) (by norm_num) rows225C_962 c142_8 (by norm_num)

theorem c142_6 : rowsJ 142 143 83 400 ≤ 813621478285463 :=
  rowsJ_le_of_split 142 143 (by norm_num) (by norm_num) rows225C_961 c142_7 (by norm_num)

theorem c142_5 : rowsJ 142 143 79 400 ≤ 814109989974538 :=
  rowsJ_le_of_split 142 143 (by norm_num) (by norm_num) rows225C_960 c142_6 (by norm_num)

theorem c142_4 : rowsJ 142 143 75 400 ≤ 817648250151454 :=
  rowsJ_le_of_split 142 143 (by norm_num) (by norm_num) rows225C_959 c142_5 (by norm_num)

theorem c142_3 : rowsJ 142 143 72 400 ≤ 822983461885458 :=
  rowsJ_le_of_split 142 143 (by norm_num) (by norm_num) rows225C_958 c142_4 (by norm_num)

theorem c142_2 : rowsJ 142 143 68 400 ≤ 830799383167173 :=
  rowsJ_le_of_split 142 143 (by norm_num) (by norm_num) rows225C_957 c142_3 (by norm_num)

theorem c142_1 : rowsJ 142 143 61 400 ≤ 840165869918596 :=
  rowsJ_le_of_split 142 143 (by norm_num) (by norm_num) rows225C_956 c142_2 (by norm_num)

theorem c142_0 : rowsJ 142 143 0 400 ≤ 1028253939391893 :=
  rowsJ_le_of_split 142 143 (by norm_num) (by norm_num) rows225C_955 c142_1 (by norm_num)

theorem hr142 : rows 142 143 ≤ 1028253939391893 := rows_le_of_rowsJ 142 143 c142_0

theorem c143_8 : rowsJ 143 144 91 400 ≤ 715409849236247 :=
  rowsJ_le_of_split 143 144 (by norm_num) (by norm_num) rows225C_973 rows225C_974 (by norm_num)

theorem c143_7 : rowsJ 143 144 86 400 ≤ 715409849236247 :=
  rowsJ_le_of_split 143 144 (by norm_num) (by norm_num) rows225C_972 c143_8 (by norm_num)

theorem c143_6 : rowsJ 143 144 82 400 ≤ 715409849236247 :=
  rowsJ_le_of_split 143 144 (by norm_num) (by norm_num) rows225C_971 c143_7 (by norm_num)

theorem c143_5 : rowsJ 143 144 78 400 ≤ 716990206387484 :=
  rowsJ_le_of_split 143 144 (by norm_num) (by norm_num) rows225C_970 c143_6 (by norm_num)

theorem c143_4 : rowsJ 143 144 74 400 ≤ 722110919567369 :=
  rowsJ_le_of_split 143 144 (by norm_num) (by norm_num) rows225C_969 c143_5 (by norm_num)

theorem c143_3 : rowsJ 143 144 71 400 ≤ 728522516169224 :=
  rowsJ_le_of_split 143 144 (by norm_num) (by norm_num) rows225C_968 c143_4 (by norm_num)

theorem c143_2 : rowsJ 143 144 67 400 ≤ 737031729516450 :=
  rowsJ_le_of_split 143 144 (by norm_num) (by norm_num) rows225C_967 c143_3 (by norm_num)

theorem c143_1 : rowsJ 143 144 61 400 ≤ 745448530324763 :=
  rowsJ_le_of_split 143 144 (by norm_num) (by norm_num) rows225C_966 c143_2 (by norm_num)

theorem c143_0 : rowsJ 143 144 0 400 ≤ 926177403423030 :=
  rowsJ_le_of_split 143 144 (by norm_num) (by norm_num) rows225C_965 c143_1 (by norm_num)

theorem hr143 : rows 143 144 ≤ 926177403423030 := rows_le_of_rowsJ 143 144 c143_0

theorem c144_8 : rowsJ 144 145 91 400 ≤ 716589110214387 :=
  rowsJ_le_of_split 144 145 (by norm_num) (by norm_num) rows225C_983 rows225C_984 (by norm_num)

theorem c144_7 : rowsJ 144 145 86 400 ≤ 716589110214387 :=
  rowsJ_le_of_split 144 145 (by norm_num) (by norm_num) rows225C_982 c144_8 (by norm_num)

theorem c144_6 : rowsJ 144 145 82 400 ≤ 716703071270017 :=
  rowsJ_le_of_split 144 145 (by norm_num) (by norm_num) rows225C_981 c144_7 (by norm_num)

theorem c144_5 : rowsJ 144 145 78 400 ≤ 718741735183023 :=
  rowsJ_le_of_split 144 145 (by norm_num) (by norm_num) rows225C_980 c144_6 (by norm_num)

theorem c144_4 : rowsJ 144 145 74 400 ≤ 724325548997471 :=
  rowsJ_le_of_split 144 145 (by norm_num) (by norm_num) rows225C_979 c144_5 (by norm_num)

theorem c144_3 : rowsJ 144 145 71 400 ≤ 731363910373620 :=
  rowsJ_le_of_split 144 145 (by norm_num) (by norm_num) rows225C_978 c144_4 (by norm_num)

theorem c144_2 : rowsJ 144 145 67 400 ≤ 740727147098679 :=
  rowsJ_le_of_split 144 145 (by norm_num) (by norm_num) rows225C_977 c144_3 (by norm_num)

theorem c144_1 : rowsJ 144 145 61 400 ≤ 750023104695293 :=
  rowsJ_le_of_split 144 145 (by norm_num) (by norm_num) rows225C_976 c144_2 (by norm_num)

theorem c144_0 : rowsJ 144 145 0 400 ≤ 922808717721080 :=
  rowsJ_le_of_split 144 145 (by norm_num) (by norm_num) rows225C_975 c144_1 (by norm_num)

theorem hr144 : rows 144 145 ≤ 922808717721080 := rows_le_of_rowsJ 144 145 c144_0

theorem c145_8 : rowsJ 145 146 94 400 ≤ 617433871214171 :=
  rowsJ_le_of_split 145 146 (by norm_num) (by norm_num) rows225C_993 rows225C_994 (by norm_num)

theorem c145_7 : rowsJ 145 146 88 400 ≤ 617433871214171 :=
  rowsJ_le_of_split 145 146 (by norm_num) (by norm_num) rows225C_992 c145_8 (by norm_num)

theorem c145_6 : rowsJ 145 146 83 400 ≤ 617534333559065 :=
  rowsJ_le_of_split 145 146 (by norm_num) (by norm_num) rows225C_991 c145_7 (by norm_num)

theorem c145_5 : rowsJ 145 146 79 400 ≤ 619305036405357 :=
  rowsJ_le_of_split 145 146 (by norm_num) (by norm_num) rows225C_990 c145_6 (by norm_num)

theorem c145_4 : rowsJ 145 146 75 400 ≤ 624280063234337 :=
  rowsJ_le_of_split 145 146 (by norm_num) (by norm_num) rows225C_989 c145_5 (by norm_num)

theorem c145_3 : rowsJ 145 146 71 400 ≤ 633697166653875 :=
  rowsJ_le_of_split 145 146 (by norm_num) (by norm_num) rows225C_988 c145_4 (by norm_num)

theorem c145_2 : rowsJ 145 146 67 400 ≤ 643976688491923 :=
  rowsJ_le_of_split 145 146 (by norm_num) (by norm_num) rows225C_987 c145_3 (by norm_num)

theorem c145_1 : rowsJ 145 146 61 400 ≤ 654244034235912 :=
  rowsJ_le_of_split 145 146 (by norm_num) (by norm_num) rows225C_986 c145_2 (by norm_num)

theorem c145_0 : rowsJ 145 146 0 400 ≤ 820166773442421 :=
  rowsJ_le_of_split 145 146 (by norm_num) (by norm_num) rows225C_985 c145_1 (by norm_num)

theorem hr145 : rows 145 146 ≤ 820166773442421 := rows_le_of_rowsJ 145 146 c145_0

theorem c146_8 : rowsJ 146 147 94 400 ≤ 618286052732411 :=
  rowsJ_le_of_split 146 147 (by norm_num) (by norm_num) rows225C_1003 rows225C_1004 (by norm_num)

theorem c146_7 : rowsJ 146 147 88 400 ≤ 618286052732411 :=
  rowsJ_le_of_split 146 147 (by norm_num) (by norm_num) rows225C_1002 c146_8 (by norm_num)

theorem c146_6 : rowsJ 146 147 83 400 ≤ 618536806486740 :=
  rowsJ_le_of_split 146 147 (by norm_num) (by norm_num) rows225C_1001 c146_7 (by norm_num)

theorem c146_5 : rowsJ 146 147 79 400 ≤ 620610259983952 :=
  rowsJ_le_of_split 146 147 (by norm_num) (by norm_num) rows225C_1000 c146_6 (by norm_num)

theorem c146_4 : rowsJ 146 147 75 400 ≤ 625891810666854 :=
  rowsJ_le_of_split 146 147 (by norm_num) (by norm_num) rows225C_999 c146_5 (by norm_num)

theorem c146_3 : rowsJ 146 147 71 400 ≤ 635808212901321 :=
  rowsJ_le_of_split 146 147 (by norm_num) (by norm_num) rows225C_998 c146_4 (by norm_num)

theorem c146_2 : rowsJ 146 147 67 400 ≤ 647013073787030 :=
  rowsJ_le_of_split 146 147 (by norm_num) (by norm_num) rows225C_997 c146_3 (by norm_num)

theorem c146_1 : rowsJ 146 147 61 400 ≤ 658260901435690 :=
  rowsJ_le_of_split 146 147 (by norm_num) (by norm_num) rows225C_996 c146_2 (by norm_num)

theorem c146_0 : rowsJ 146 147 0 400 ≤ 816725946229187 :=
  rowsJ_le_of_split 146 147 (by norm_num) (by norm_num) rows225C_995 c146_1 (by norm_num)

theorem hr146 : rows 146 147 ≤ 816725946229187 := rows_le_of_rowsJ 146 147 c146_0

theorem c147_8 : rowsJ 147 148 93 400 ≤ 518126039486484 :=
  rowsJ_le_of_split 147 148 (by norm_num) (by norm_num) rows225C_1013 rows225C_1014 (by norm_num)

theorem c147_7 : rowsJ 147 148 87 400 ≤ 518126039486484 :=
  rowsJ_le_of_split 147 148 (by norm_num) (by norm_num) rows225C_1012 c147_8 (by norm_num)

theorem c147_6 : rowsJ 147 148 82 400 ≤ 518916208459359 :=
  rowsJ_le_of_split 147 148 (by norm_num) (by norm_num) rows225C_1011 c147_7 (by norm_num)

theorem c147_5 : rowsJ 147 148 78 400 ≤ 521916645982749 :=
  rowsJ_le_of_split 147 148 (by norm_num) (by norm_num) rows225C_1010 c147_6 (by norm_num)

theorem c147_4 : rowsJ 147 148 74 400 ≤ 528475750259090 :=
  rowsJ_le_of_split 147 148 (by norm_num) (by norm_num) rows225C_1009 c147_5 (by norm_num)

theorem c147_3 : rowsJ 147 148 70 400 ≤ 539819462612913 :=
  rowsJ_le_of_split 147 148 (by norm_num) (by norm_num) rows225C_1008 c147_4 (by norm_num)

theorem c147_2 : rowsJ 147 148 66 400 ≤ 551463924384351 :=
  rowsJ_le_of_split 147 148 (by norm_num) (by norm_num) rows225C_1007 c147_3 (by norm_num)

theorem c147_1 : rowsJ 147 148 60 400 ≤ 562257892126778 :=
  rowsJ_le_of_split 147 148 (by norm_num) (by norm_num) rows225C_1006 c147_2 (by norm_num)

theorem c147_0 : rowsJ 147 148 0 400 ≤ 713264794253321 :=
  rowsJ_le_of_split 147 148 (by norm_num) (by norm_num) rows225C_1005 c147_1 (by norm_num)

theorem hr147 : rows 147 148 ≤ 713264794253321 := rows_le_of_rowsJ 147 148 c147_0

theorem c148_7 : rowsJ 148 149 87 400 ≤ 518662902816923 :=
  rowsJ_le_of_split 148 149 (by norm_num) (by norm_num) rows225C_1022 rows225C_1023 (by norm_num)

theorem c148_6 : rowsJ 148 149 82 400 ≤ 519639648531265 :=
  rowsJ_le_of_split 148 149 (by norm_num) (by norm_num) rows225C_1021 c148_7 (by norm_num)

theorem c148_5 : rowsJ 148 149 78 400 ≤ 522791871682454 :=
  rowsJ_le_of_split 148 149 (by norm_num) (by norm_num) rows225C_1020 c148_6 (by norm_num)

theorem c148_4 : rowsJ 148 149 74 400 ≤ 529506085198758 :=
  rowsJ_le_of_split 148 149 (by norm_num) (by norm_num) rows225C_1019 c148_5 (by norm_num)

theorem c148_3 : rowsJ 148 149 70 400 ≤ 541239995617035 :=
  rowsJ_le_of_split 148 149 (by norm_num) (by norm_num) rows225C_1018 c148_4 (by norm_num)

theorem c148_2 : rowsJ 148 149 66 400 ≤ 553828169679372 :=
  rowsJ_le_of_split 148 149 (by norm_num) (by norm_num) rows225C_1017 c148_3 (by norm_num)

theorem c148_1 : rowsJ 148 149 60 400 ≤ 565626317071868 :=
  rowsJ_le_of_split 148 149 (by norm_num) (by norm_num) rows225C_1016 c148_2 (by norm_num)

theorem c148_0 : rowsJ 148 149 0 400 ≤ 709573044269658 :=
  rowsJ_le_of_split 148 149 (by norm_num) (by norm_num) rows225C_1015 c148_1 (by norm_num)

theorem hr148 : rows 148 149 ≤ 709573044269658 := rows_le_of_rowsJ 148 149 c148_0

theorem c149_7 : rowsJ 149 150 88 400 ≤ 417467800269294 :=
  rowsJ_le_of_split 149 150 (by norm_num) (by norm_num) rows225C_1031 rows225C_1032 (by norm_num)

theorem c149_6 : rowsJ 149 150 83 400 ≤ 418178232636417 :=
  rowsJ_le_of_split 149 150 (by norm_num) (by norm_num) rows225C_1030 c149_7 (by norm_num)

theorem c149_5 : rowsJ 149 150 78 400 ≤ 421848463204000 :=
  rowsJ_le_of_split 149 150 (by norm_num) (by norm_num) rows225C_1029 c149_6 (by norm_num)

theorem c149_4 : rowsJ 149 150 74 400 ≤ 428669013862707 :=
  rowsJ_le_of_split 149 150 (by norm_num) (by norm_num) rows225C_1028 c149_5 (by norm_num)

theorem c149_3 : rowsJ 149 150 70 400 ≤ 440513858621751 :=
  rowsJ_le_of_split 149 150 (by norm_num) (by norm_num) rows225C_1027 c149_4 (by norm_num)

theorem c149_2 : rowsJ 149 150 66 400 ≤ 454111884321185 :=
  rowsJ_le_of_split 149 150 (by norm_num) (by norm_num) rows225C_1026 c149_3 (by norm_num)

theorem c149_1 : rowsJ 149 150 60 400 ≤ 467011778440838 :=
  rowsJ_le_of_split 149 150 (by norm_num) (by norm_num) rows225C_1025 c149_2 (by norm_num)

theorem c149_0 : rowsJ 149 150 0 400 ≤ 604995610268039 :=
  rowsJ_le_of_split 149 150 (by norm_num) (by norm_num) rows225C_1024 c149_1 (by norm_num)

theorem hr149 : rows 149 150 ≤ 604995610268039 := rows_le_of_rowsJ 149 150 c149_0

theorem c150_7 : rowsJ 150 151 89 400 ≤ 417704648898128 :=
  rowsJ_le_of_split 150 151 (by norm_num) (by norm_num) rows225C_1040 rows225C_1041 (by norm_num)

theorem c150_6 : rowsJ 150 151 83 400 ≤ 418415507032726 :=
  rowsJ_le_of_split 150 151 (by norm_num) (by norm_num) rows225C_1039 c150_7 (by norm_num)

theorem c150_5 : rowsJ 150 151 78 400 ≤ 422088545613819 :=
  rowsJ_le_of_split 150 151 (by norm_num) (by norm_num) rows225C_1038 c150_6 (by norm_num)

theorem c150_4 : rowsJ 150 151 74 400 ≤ 428914294892199 :=
  rowsJ_le_of_split 150 151 (by norm_num) (by norm_num) rows225C_1037 c150_5 (by norm_num)

theorem c150_3 : rowsJ 150 151 70 400 ≤ 440767825600387 :=
  rowsJ_le_of_split 150 151 (by norm_num) (by norm_num) rows225C_1036 c150_4 (by norm_num)

theorem c150_2 : rowsJ 150 151 66 400 ≤ 455386524279062 :=
  rowsJ_le_of_split 150 151 (by norm_num) (by norm_num) rows225C_1035 c150_3 (by norm_num)

theorem c150_1 : rowsJ 150 151 60 400 ≤ 469399256470823 :=
  rowsJ_le_of_split 150 151 (by norm_num) (by norm_num) rows225C_1034 c150_2 (by norm_num)

theorem c150_0 : rowsJ 150 151 0 400 ≤ 600884752464746 :=
  rowsJ_le_of_split 150 151 (by norm_num) (by norm_num) rows225C_1033 c150_1 (by norm_num)

theorem hr150 : rows 150 151 ≤ 600884752464746 := rows_le_of_rowsJ 150 151 c150_0

theorem c151_7 : rowsJ 151 152 89 400 ≤ 315413875702631 :=
  rowsJ_le_of_split 151 152 (by norm_num) (by norm_num) rows225C_1049 rows225C_1050 (by norm_num)

theorem c151_6 : rowsJ 151 152 83 400 ≤ 316064844518701 :=
  rowsJ_le_of_split 151 152 (by norm_num) (by norm_num) rows225C_1048 c151_7 (by norm_num)

theorem c151_5 : rowsJ 151 152 78 400 ≤ 319681083620256 :=
  rowsJ_le_of_split 151 152 (by norm_num) (by norm_num) rows225C_1047 c151_6 (by norm_num)

theorem c151_4 : rowsJ 151 152 74 400 ≤ 326464870389713 :=
  rowsJ_le_of_split 151 152 (by norm_num) (by norm_num) rows225C_1046 c151_5 (by norm_num)

theorem c151_3 : rowsJ 151 152 70 400 ≤ 338280407804550 :=
  rowsJ_le_of_split 151 152 (by norm_num) (by norm_num) rows225C_1045 c151_4 (by norm_num)

theorem c151_2 : rowsJ 151 152 66 400 ≤ 353685606973889 :=
  rowsJ_le_of_split 151 152 (by norm_num) (by norm_num) rows225C_1044 c151_3 (by norm_num)

theorem c151_1 : rowsJ 151 152 60 400 ≤ 368911783868443 :=
  rowsJ_le_of_split 151 152 (by norm_num) (by norm_num) rows225C_1043 c151_2 (by norm_num)

theorem c151_0 : rowsJ 151 152 0 400 ≤ 494972108704959 :=
  rowsJ_le_of_split 151 152 (by norm_num) (by norm_num) rows225C_1042 c151_1 (by norm_num)

theorem hr151 : rows 151 152 ≤ 494972108704959 := rows_le_of_rowsJ 151 152 c151_0

theorem c152_7 : rowsJ 152 153 88 400 ≤ 315369991478012 :=
  rowsJ_le_of_split 152 153 (by norm_num) (by norm_num) rows225C_1058 rows225C_1059 (by norm_num)

theorem c152_6 : rowsJ 152 153 82 400 ≤ 316242027855393 :=
  rowsJ_le_of_split 152 153 (by norm_num) (by norm_num) rows225C_1057 c152_7 (by norm_num)

theorem c152_5 : rowsJ 152 153 77 400 ≤ 320581213918070 :=
  rowsJ_le_of_split 152 153 (by norm_num) (by norm_num) rows225C_1056 c152_6 (by norm_num)

theorem c152_4 : rowsJ 152 153 73 400 ≤ 328339507620067 :=
  rowsJ_le_of_split 152 153 (by norm_num) (by norm_num) rows225C_1055 c152_5 (by norm_num)

theorem c152_3 : rowsJ 152 153 69 400 ≤ 341517151683316 :=
  rowsJ_le_of_split 152 153 (by norm_num) (by norm_num) rows225C_1054 c152_4 (by norm_num)

theorem c152_2 : rowsJ 152 153 65 400 ≤ 357373977469849 :=
  rowsJ_le_of_split 152 153 (by norm_num) (by norm_num) rows225C_1053 c152_3 (by norm_num)

theorem c152_1 : rowsJ 152 153 59 400 ≤ 371863488765734 :=
  rowsJ_le_of_split 152 153 (by norm_num) (by norm_num) rows225C_1052 c152_2 (by norm_num)

theorem c152_0 : rowsJ 152 153 0 400 ≤ 490344624210507 :=
  rowsJ_le_of_split 152 153 (by norm_num) (by norm_num) rows225C_1051 c152_1 (by norm_num)

theorem hr152 : rows 152 153 ≤ 490344624210507 := rows_le_of_rowsJ 152 153 c152_0

theorem c153_7 : rowsJ 153 154 88 400 ≤ 211955166072009 :=
  rowsJ_le_of_split 153 154 (by norm_num) (by norm_num) rows225C_1067 rows225C_1068 (by norm_num)

theorem c153_6 : rowsJ 153 154 82 400 ≤ 212657585350594 :=
  rowsJ_le_of_split 153 154 (by norm_num) (by norm_num) rows225C_1066 c153_7 (by norm_num)

theorem c153_5 : rowsJ 153 154 77 400 ≤ 216758576293542 :=
  rowsJ_le_of_split 153 154 (by norm_num) (by norm_num) rows225C_1065 c153_6 (by norm_num)

theorem c153_4 : rowsJ 153 154 73 400 ≤ 224329479950595 :=
  rowsJ_le_of_split 153 154 (by norm_num) (by norm_num) rows225C_1064 c153_5 (by norm_num)

theorem c153_3 : rowsJ 153 154 69 400 ≤ 237323319439609 :=
  rowsJ_le_of_split 153 154 (by norm_num) (by norm_num) rows225C_1063 c153_4 (by norm_num)

theorem c153_2 : rowsJ 153 154 65 400 ≤ 253948644624780 :=
  rowsJ_le_of_split 153 154 (by norm_num) (by norm_num) rows225C_1062 c153_3 (by norm_num)

theorem c153_1 : rowsJ 153 154 59 400 ≤ 269683180642615 :=
  rowsJ_le_of_split 153 154 (by norm_num) (by norm_num) rows225C_1061 c153_2 (by norm_num)

theorem c153_0 : rowsJ 153 154 0 400 ≤ 383155533033401 :=
  rowsJ_le_of_split 153 154 (by norm_num) (by norm_num) rows225C_1060 c153_1 (by norm_num)

theorem hr153 : rows 153 154 ≤ 383155533033401 := rows_le_of_rowsJ 153 154 c153_0

theorem c154_7 : rowsJ 154 155 87 400 ≤ 211654401953843 :=
  rowsJ_le_of_split 154 155 (by norm_num) (by norm_num) rows225C_1076 rows225C_1077 (by norm_num)

theorem c154_6 : rowsJ 154 155 81 400 ≤ 212559347216480 :=
  rowsJ_le_of_split 154 155 (by norm_num) (by norm_num) rows225C_1075 c154_7 (by norm_num)

theorem c154_5 : rowsJ 154 155 76 400 ≤ 217304260118873 :=
  rowsJ_le_of_split 154 155 (by norm_num) (by norm_num) rows225C_1074 c154_6 (by norm_num)

theorem c154_4 : rowsJ 154 155 72 400 ≤ 225798980064339 :=
  rowsJ_le_of_split 154 155 (by norm_num) (by norm_num) rows225C_1073 c154_5 (by norm_num)

theorem c154_3 : rowsJ 154 155 68 400 ≤ 240112726164891 :=
  rowsJ_le_of_split 154 155 (by norm_num) (by norm_num) rows225C_1072 c154_4 (by norm_num)

theorem c154_2 : rowsJ 154 155 64 400 ≤ 257026885862270 :=
  rowsJ_le_of_split 154 155 (by norm_num) (by norm_num) rows225C_1071 c154_3 (by norm_num)

theorem c154_1 : rowsJ 154 155 59 400 ≤ 270272163946798 :=
  rowsJ_le_of_split 154 155 (by norm_num) (by norm_num) rows225C_1070 c154_2 (by norm_num)

theorem c154_0 : rowsJ 154 155 0 400 ≤ 378180306971896 :=
  rowsJ_le_of_split 154 155 (by norm_num) (by norm_num) rows225C_1069 c154_1 (by norm_num)

theorem hr154 : rows 154 155 ≤ 378180306971896 := rows_le_of_rowsJ 154 155 c154_0

theorem c155_7 : rowsJ 155 156 88 400 ≤ 106970197226489 :=
  rowsJ_le_of_split 155 156 (by norm_num) (by norm_num) rows225C_1085 rows225C_1086 (by norm_num)

theorem c155_6 : rowsJ 155 156 82 400 ≤ 107362300612984 :=
  rowsJ_le_of_split 155 156 (by norm_num) (by norm_num) rows225C_1084 c155_7 (by norm_num)

theorem c155_5 : rowsJ 155 156 77 400 ≤ 110717057308413 :=
  rowsJ_le_of_split 155 156 (by norm_num) (by norm_num) rows225C_1083 c155_6 (by norm_num)

theorem c155_4 : rowsJ 155 156 72 400 ≤ 120191780948680 :=
  rowsJ_le_of_split 155 156 (by norm_num) (by norm_num) rows225C_1082 c155_5 (by norm_num)

theorem c155_3 : rowsJ 155 156 68 400 ≤ 134177511394178 :=
  rowsJ_le_of_split 155 156 (by norm_num) (by norm_num) rows225C_1081 c155_4 (by norm_num)

theorem c155_2 : rowsJ 155 156 64 400 ≤ 151844175982165 :=
  rowsJ_le_of_split 155 156 (by norm_num) (by norm_num) rows225C_1080 c155_3 (by norm_num)

theorem c155_1 : rowsJ 155 156 58 400 ≤ 168017840200236 :=
  rowsJ_le_of_split 155 156 (by norm_num) (by norm_num) rows225C_1079 c155_2 (by norm_num)

theorem c155_0 : rowsJ 155 156 0 400 ≤ 269625556773134 :=
  rowsJ_le_of_split 155 156 (by norm_num) (by norm_num) rows225C_1078 c155_1 (by norm_num)

theorem hr155 : rows 155 156 ≤ 269625556773134 := rows_le_of_rowsJ 155 156 c155_0

theorem c156_6 : rowsJ 156 157 83 400 ≤ 106590059981499 :=
  rowsJ_le_of_split 156 157 (by norm_num) (by norm_num) rows225C_1093 rows225C_1094 (by norm_num)

theorem c156_5 : rowsJ 156 157 77 400 ≤ 109675389427679 :=
  rowsJ_le_of_split 156 157 (by norm_num) (by norm_num) rows225C_1092 c156_6 (by norm_num)

theorem c156_4 : rowsJ 156 157 72 400 ≤ 118610366955525 :=
  rowsJ_le_of_split 156 157 (by norm_num) (by norm_num) rows225C_1091 c156_5 (by norm_num)

theorem c156_3 : rowsJ 156 157 68 400 ≤ 132166691989842 :=
  rowsJ_le_of_split 156 157 (by norm_num) (by norm_num) rows225C_1090 c156_4 (by norm_num)

theorem c156_2 : rowsJ 156 157 64 400 ≤ 150570163115865 :=
  rowsJ_le_of_split 156 157 (by norm_num) (by norm_num) rows225C_1089 c156_3 (by norm_num)

theorem c156_1 : rowsJ 156 157 58 400 ≤ 168036286412006 :=
  rowsJ_le_of_split 156 157 (by norm_num) (by norm_num) rows225C_1088 c156_2 (by norm_num)

theorem c156_0 : rowsJ 156 157 0 400 ≤ 264515785347589 :=
  rowsJ_le_of_split 156 157 (by norm_num) (by norm_num) rows225C_1087 c156_1 (by norm_num)

theorem hr156 : rows 156 157 ≤ 264515785347589 := rows_le_of_rowsJ 156 157 c156_0

theorem c157_6 : rowsJ 157 158 82 400 ≤ 820622524543 :=
  rowsJ_le_of_split 157 158 (by norm_num) (by norm_num) rows225C_1101 rows225C_1102 (by norm_num)

theorem c157_5 : rowsJ 157 158 76 400 ≤ 4472868697134 :=
  rowsJ_le_of_split 157 158 (by norm_num) (by norm_num) rows225C_1100 c157_6 (by norm_num)

theorem c157_4 : rowsJ 157 158 71 400 ≤ 14393854601629 :=
  rowsJ_le_of_split 157 158 (by norm_num) (by norm_num) rows225C_1099 c157_5 (by norm_num)

theorem c157_3 : rowsJ 157 158 67 400 ≤ 29189987590871 :=
  rowsJ_le_of_split 157 158 (by norm_num) (by norm_num) rows225C_1098 c157_4 (by norm_num)

theorem c157_2 : rowsJ 157 158 63 400 ≤ 47724005351354 :=
  rowsJ_le_of_split 157 158 (by norm_num) (by norm_num) rows225C_1097 c157_3 (by norm_num)

theorem c157_1 : rowsJ 157 158 58 400 ≤ 62437432553658 :=
  rowsJ_le_of_split 157 158 (by norm_num) (by norm_num) rows225C_1096 c157_2 (by norm_num)

theorem c157_0 : rowsJ 157 158 0 400 ≤ 154834204333103 :=
  rowsJ_le_of_split 157 158 (by norm_num) (by norm_num) rows225C_1095 c157_1 (by norm_num)

theorem hr157 : rows 157 158 ≤ 154834204333103 := rows_le_of_rowsJ 157 158 c157_0

theorem c158_6 : rowsJ 158 159 82 400 ≤ 108284851960 :=
  rowsJ_le_of_split 158 159 (by norm_num) (by norm_num) rows225C_1109 rows225C_1110 (by norm_num)

theorem c158_5 : rowsJ 158 159 76 400 ≤ 3270548344892 :=
  rowsJ_le_of_split 158 159 (by norm_num) (by norm_num) rows225C_1108 c158_6 (by norm_num)

theorem c158_4 : rowsJ 158 159 71 400 ≤ 12506116041573 :=
  rowsJ_le_of_split 158 159 (by norm_num) (by norm_num) rows225C_1107 c158_5 (by norm_num)

theorem c158_3 : rowsJ 158 159 67 400 ≤ 26729792328883 :=
  rowsJ_le_of_split 158 159 (by norm_num) (by norm_num) rows225C_1106 c158_4 (by norm_num)

theorem c158_2 : rowsJ 158 159 63 400 ≤ 45987048902893 :=
  rowsJ_le_of_split 158 159 (by norm_num) (by norm_num) rows225C_1105 c158_3 (by norm_num)

theorem c158_1 : rowsJ 158 159 58 400 ≤ 61845302484585 :=
  rowsJ_le_of_split 158 159 (by norm_num) (by norm_num) rows225C_1104 c158_2 (by norm_num)

theorem c158_0 : rowsJ 158 159 0 400 ≤ 149673925422190 :=
  rowsJ_le_of_split 158 159 (by norm_num) (by norm_num) rows225C_1103 c158_1 (by norm_num)

theorem hr158 : rows 158 159 ≤ 149673925422190 := rows_le_of_rowsJ 158 159 c158_0

theorem c159_6 : rowsJ 159 160 82 400 ≤ 109590879741690 :=
  rowsJ_le_of_split 159 160 (by norm_num) (by norm_num) rows225C_1117 rows225C_1118 (by norm_num)

theorem c159_5 : rowsJ 159 160 76 400 ≤ 112335768793111 :=
  rowsJ_le_of_split 159 160 (by norm_num) (by norm_num) rows225C_1116 c159_6 (by norm_num)

theorem c159_4 : rowsJ 159 160 71 400 ≤ 120909702829122 :=
  rowsJ_le_of_split 159 160 (by norm_num) (by norm_num) rows225C_1115 c159_5 (by norm_num)

theorem c159_3 : rowsJ 159 160 67 400 ≤ 134519914372263 :=
  rowsJ_le_of_split 159 160 (by norm_num) (by norm_num) rows225C_1114 c159_4 (by norm_num)

theorem c159_2 : rowsJ 159 160 63 400 ≤ 154072449061140 :=
  rowsJ_le_of_split 159 160 (by norm_num) (by norm_num) rows225C_1113 c159_3 (by norm_num)

theorem c159_1 : rowsJ 159 160 57 400 ≤ 173429189361026 :=
  rowsJ_le_of_split 159 160 (by norm_num) (by norm_num) rows225C_1112 c159_2 (by norm_num)

theorem c159_0 : rowsJ 159 160 0 400 ≤ 255539504430866 :=
  rowsJ_le_of_split 159 160 (by norm_num) (by norm_num) rows225C_1111 c159_1 (by norm_num)

theorem hr159 : rows 159 160 ≤ 255539504430866 := rows_le_of_rowsJ 159 160 c159_0

theorem c160_6 : rowsJ 160 161 81 400 ≤ 218192812137285 :=
  rowsJ_le_of_split 160 161 (by norm_num) (by norm_num) rows225C_1125 rows225C_1126 (by norm_num)

theorem c160_5 : rowsJ 160 161 75 400 ≤ 221435126384093 :=
  rowsJ_le_of_split 160 161 (by norm_num) (by norm_num) rows225C_1124 c160_6 (by norm_num)

theorem c160_4 : rowsJ 160 161 70 400 ≤ 230905294337730 :=
  rowsJ_le_of_split 160 161 (by norm_num) (by norm_num) rows225C_1123 c160_5 (by norm_num)

theorem c160_3 : rowsJ 160 161 66 400 ≤ 245620402060938 :=
  rowsJ_le_of_split 160 161 (by norm_num) (by norm_num) rows225C_1122 c160_4 (by norm_num)

theorem c160_2 : rowsJ 160 161 62 400 ≤ 265574108757781 :=
  rowsJ_le_of_split 160 161 (by norm_num) (by norm_num) rows225C_1121 c160_3 (by norm_num)

theorem c160_1 : rowsJ 160 161 57 400 ≤ 281845863313506 :=
  rowsJ_le_of_split 160 161 (by norm_num) (by norm_num) rows225C_1120 c160_2 (by norm_num)

theorem c160_0 : rowsJ 160 161 0 400 ≤ 359800091753097 :=
  rowsJ_le_of_split 160 161 (by norm_num) (by norm_num) rows225C_1119 c160_1 (by norm_num)

theorem hr160 : rows 160 161 ≤ 359800091753097 := rows_le_of_rowsJ 160 161 c160_0

theorem c161_6 : rowsJ 161 162 82 400 ≤ 325718376126011 :=
  rowsJ_le_of_split 161 162 (by norm_num) (by norm_num) rows225C_1133 rows225C_1134 (by norm_num)

theorem c161_5 : rowsJ 161 162 76 400 ≤ 327681768474726 :=
  rowsJ_le_of_split 161 162 (by norm_num) (by norm_num) rows225C_1132 c161_6 (by norm_num)

theorem c161_4 : rowsJ 161 162 71 400 ≤ 334955759562427 :=
  rowsJ_le_of_split 161 162 (by norm_num) (by norm_num) rows225C_1131 c161_5 (by norm_num)

theorem c161_3 : rowsJ 161 162 66 400 ≤ 351374822531717 :=
  rowsJ_le_of_split 161 162 (by norm_num) (by norm_num) rows225C_1130 c161_4 (by norm_num)

theorem c161_2 : rowsJ 161 162 62 400 ≤ 371570074794177 :=
  rowsJ_le_of_split 161 162 (by norm_num) (by norm_num) rows225C_1129 c161_3 (by norm_num)

theorem c161_1 : rowsJ 161 162 57 400 ≤ 389116220301778 :=
  rowsJ_le_of_split 161 162 (by norm_num) (by norm_num) rows225C_1128 c161_2 (by norm_num)

theorem c161_0 : rowsJ 161 162 0 400 ≤ 463975251558348 :=
  rowsJ_le_of_split 161 162 (by norm_num) (by norm_num) rows225C_1127 c161_1 (by norm_num)

theorem hr161 : rows 161 162 ≤ 463975251558348 := rows_le_of_rowsJ 161 162 c161_0

theorem c162_5 : rowsJ 162 163 77 400 ≤ 433414703378761 :=
  rowsJ_le_of_split 162 163 (by norm_num) (by norm_num) rows225C_1140 rows225C_1141 (by norm_num)

theorem c162_4 : rowsJ 162 163 71 400 ≤ 440652563449487 :=
  rowsJ_le_of_split 162 163 (by norm_num) (by norm_num) rows225C_1139 c162_5 (by norm_num)

theorem c162_3 : rowsJ 162 163 66 400 ≤ 456157980135447 :=
  rowsJ_le_of_split 162 163 (by norm_num) (by norm_num) rows225C_1138 c162_4 (by norm_num)

theorem c162_2 : rowsJ 162 163 62 400 ≤ 476551192682084 :=
  rowsJ_le_of_split 162 163 (by norm_num) (by norm_num) rows225C_1137 c162_3 (by norm_num)

theorem c162_1 : rowsJ 162 163 56 400 ≤ 497916187280177 :=
  rowsJ_le_of_split 162 163 (by norm_num) (by norm_num) rows225C_1136 c162_2 (by norm_num)

theorem c162_0 : rowsJ 162 163 0 400 ≤ 566744978890343 :=
  rowsJ_le_of_split 162 163 (by norm_num) (by norm_num) rows225C_1135 c162_1 (by norm_num)

theorem hr162 : rows 162 163 ≤ 566744978890343 := rows_le_of_rowsJ 162 163 c162_0

theorem c163_5 : rowsJ 163 164 76 400 ≤ 539557087569101 :=
  rowsJ_le_of_split 163 164 (by norm_num) (by norm_num) rows225C_1147 rows225C_1148 (by norm_num)

theorem c163_4 : rowsJ 163 164 70 400 ≤ 547731409335308 :=
  rowsJ_le_of_split 163 164 (by norm_num) (by norm_num) rows225C_1146 c163_5 (by norm_num)

theorem c163_3 : rowsJ 163 164 65 400 ≤ 564578807079001 :=
  rowsJ_le_of_split 163 164 (by norm_num) (by norm_num) rows225C_1145 c163_4 (by norm_num)

theorem c163_2 : rowsJ 163 164 61 400 ≤ 585315270598560 :=
  rowsJ_le_of_split 163 164 (by norm_num) (by norm_num) rows225C_1144 c163_3 (by norm_num)

theorem c163_1 : rowsJ 163 164 56 400 ≤ 603328597806250 :=
  rowsJ_le_of_split 163 164 (by norm_num) (by norm_num) rows225C_1143 c163_2 (by norm_num)

theorem c163_0 : rowsJ 163 164 0 400 ≤ 669456295585429 :=
  rowsJ_le_of_split 163 164 (by norm_num) (by norm_num) rows225C_1142 c163_1 (by norm_num)

theorem hr163 : rows 163 164 ≤ 669456295585429 := rows_le_of_rowsJ 163 164 c163_0

theorem c164_5 : rowsJ 164 165 76 400 ≤ 644228294462955 :=
  rowsJ_le_of_split 164 165 (by norm_num) (by norm_num) rows225C_1154 rows225C_1155 (by norm_num)

theorem c164_4 : rowsJ 164 165 70 400 ≤ 651655246396282 :=
  rowsJ_le_of_split 164 165 (by norm_num) (by norm_num) rows225C_1153 c164_5 (by norm_num)

theorem c164_3 : rowsJ 164 165 65 400 ≤ 667567913099523 :=
  rowsJ_le_of_split 164 165 (by norm_num) (by norm_num) rows225C_1152 c164_4 (by norm_num)

theorem c164_2 : rowsJ 164 165 61 400 ≤ 688500563217108 :=
  rowsJ_le_of_split 164 165 (by norm_num) (by norm_num) rows225C_1151 c164_3 (by norm_num)

theorem c164_1 : rowsJ 164 165 56 400 ≤ 707840981667670 :=
  rowsJ_le_of_split 164 165 (by norm_num) (by norm_num) rows225C_1150 c164_2 (by norm_num)

theorem c164_0 : rowsJ 164 165 0 400 ≤ 770853713582907 :=
  rowsJ_le_of_split 164 165 (by norm_num) (by norm_num) rows225C_1149 c164_1 (by norm_num)

theorem hr164 : rows 164 165 ≤ 770853713582907 := rows_le_of_rowsJ 164 165 c164_0

theorem c165_5 : rowsJ 165 166 76 400 ≤ 748144298472284 :=
  rowsJ_le_of_split 165 166 (by norm_num) (by norm_num) rows225C_1161 rows225C_1162 (by norm_num)

theorem c165_4 : rowsJ 165 166 70 400 ≤ 754897948820078 :=
  rowsJ_le_of_split 165 166 (by norm_num) (by norm_num) rows225C_1160 c165_5 (by norm_num)

theorem c165_3 : rowsJ 165 166 65 400 ≤ 769933068275685 :=
  rowsJ_le_of_split 165 166 (by norm_num) (by norm_num) rows225C_1159 c165_4 (by norm_num)

theorem c165_2 : rowsJ 165 166 61 400 ≤ 790547050930149 :=
  rowsJ_le_of_split 165 166 (by norm_num) (by norm_num) rows225C_1158 c165_3 (by norm_num)

theorem c165_1 : rowsJ 165 166 55 400 ≤ 814152871379096 :=
  rowsJ_le_of_split 165 166 (by norm_num) (by norm_num) rows225C_1157 c165_2 (by norm_num)

theorem c165_0 : rowsJ 165 166 0 400 ≤ 872293431984248 :=
  rowsJ_le_of_split 165 166 (by norm_num) (by norm_num) rows225C_1156 c165_1 (by norm_num)

theorem hr165 : rows 165 166 ≤ 872293431984248 := rows_le_of_rowsJ 165 166 c165_0

theorem c166_5 : rowsJ 166 167 76 400 ≤ 851240631547590 :=
  rowsJ_le_of_split 166 167 (by norm_num) (by norm_num) rows225C_1168 rows225C_1169 (by norm_num)

theorem c166_4 : rowsJ 166 167 70 400 ≤ 857302378530981 :=
  rowsJ_le_of_split 166 167 (by norm_num) (by norm_num) rows225C_1167 c166_5 (by norm_num)

theorem c166_3 : rowsJ 166 167 65 400 ≤ 871436386727407 :=
  rowsJ_le_of_split 166 167 (by norm_num) (by norm_num) rows225C_1166 c166_4 (by norm_num)

theorem c166_2 : rowsJ 166 167 60 400 ≤ 897147839216849 :=
  rowsJ_le_of_split 166 167 (by norm_num) (by norm_num) rows225C_1165 c166_3 (by norm_num)

theorem c166_1 : rowsJ 166 167 55 400 ≤ 917014015789301 :=
  rowsJ_le_of_split 166 167 (by norm_num) (by norm_num) rows225C_1164 c166_2 (by norm_num)

theorem c166_0 : rowsJ 166 167 0 400 ≤ 972458314068628 :=
  rowsJ_le_of_split 166 167 (by norm_num) (by norm_num) rows225C_1163 c166_1 (by norm_num)

theorem hr166 : rows 166 167 ≤ 972458314068628 := rows_le_of_rowsJ 166 167 c166_0

theorem c167_5 : rowsJ 167 168 76 400 ≤ 953617751592779 :=
  rowsJ_le_of_split 167 168 (by norm_num) (by norm_num) rows225C_1175 rows225C_1176 (by norm_num)

theorem c167_4 : rowsJ 167 168 70 400 ≤ 959064640601894 :=
  rowsJ_le_of_split 167 168 (by norm_num) (by norm_num) rows225C_1174 c167_5 (by norm_num)

theorem c167_3 : rowsJ 167 168 65 400 ≤ 972356704518516 :=
  rowsJ_le_of_split 167 168 (by norm_num) (by norm_num) rows225C_1173 c167_4 (by norm_num)

theorem c167_2 : rowsJ 167 168 60 400 ≤ 997542806727656 :=
  rowsJ_le_of_split 167 168 (by norm_num) (by norm_num) rows225C_1172 c167_3 (by norm_num)

theorem c167_1 : rowsJ 167 168 55 400 ≤ 1018882490978925 :=
  rowsJ_le_of_split 167 168 (by norm_num) (by norm_num) rows225C_1171 c167_2 (by norm_num)

theorem c167_0 : rowsJ 167 168 0 400 ≤ 1072652619574272 :=
  rowsJ_le_of_split 167 168 (by norm_num) (by norm_num) rows225C_1170 c167_1 (by norm_num)

theorem hr167 : rows 167 168 ≤ 1072652619574272 := rows_le_of_rowsJ 167 168 c167_0

theorem c168_4 : rowsJ 168 169 71 400 ≤ 1053346308402425 :=
  rowsJ_le_of_split 168 169 (by norm_num) (by norm_num) rows225C_1181 rows225C_1182 (by norm_num)

theorem c168_3 : rowsJ 168 169 65 400 ≤ 1067176164766151 :=
  rowsJ_le_of_split 168 169 (by norm_num) (by norm_num) rows225C_1180 c168_4 (by norm_num)

theorem c168_2 : rowsJ 168 169 60 400 ≤ 1091818305666397 :=
  rowsJ_le_of_split 168 169 (by norm_num) (by norm_num) rows225C_1179 c168_3 (by norm_num)

theorem c168_1 : rowsJ 168 169 54 400 ≤ 1117809946191454 :=
  rowsJ_le_of_split 168 169 (by norm_num) (by norm_num) rows225C_1178 c168_2 (by norm_num)

theorem c168_0 : rowsJ 168 169 0 400 ≤ 1166424952966999 :=
  rowsJ_le_of_split 168 169 (by norm_num) (by norm_num) rows225C_1177 c168_1 (by norm_num)

theorem hr168 : rows 168 169 ≤ 1166424952966999 := rows_le_of_rowsJ 168 169 c168_0

theorem c169_4 : rowsJ 169 170 70 400 ≤ 1150380295908224 :=
  rowsJ_le_of_split 169 170 (by norm_num) (by norm_num) rows225C_1187 rows225C_1188 (by norm_num)

theorem c169_3 : rowsJ 169 170 64 400 ≤ 1165615970582714 :=
  rowsJ_le_of_split 169 170 (by norm_num) (by norm_num) rows225C_1186 c169_4 (by norm_num)

theorem c169_2 : rowsJ 169 170 59 400 ≤ 1191492462133511 :=
  rowsJ_le_of_split 169 170 (by norm_num) (by norm_num) rows225C_1185 c169_3 (by norm_num)

theorem c169_1 : rowsJ 169 170 54 400 ≤ 1213424409891687 :=
  rowsJ_le_of_split 169 170 (by norm_num) (by norm_num) rows225C_1184 c169_2 (by norm_num)

theorem c169_0 : rowsJ 169 170 0 400 ≤ 1260760640600047 :=
  rowsJ_le_of_split 169 170 (by norm_num) (by norm_num) rows225C_1183 c169_1 (by norm_num)

theorem hr169 : rows 169 170 ≤ 1260760640600047 := rows_le_of_rowsJ 169 170 c169_0

theorem c170_4 : rowsJ 170 171 70 400 ≤ 1245812886819263 :=
  rowsJ_le_of_split 170 171 (by norm_num) (by norm_num) rows225C_1193 rows225C_1194 (by norm_num)

theorem c170_3 : rowsJ 170 171 64 400 ≤ 1260021489024530 :=
  rowsJ_le_of_split 170 171 (by norm_num) (by norm_num) rows225C_1192 c170_4 (by norm_num)

theorem c170_2 : rowsJ 170 171 59 400 ≤ 1285343512689776 :=
  rowsJ_le_of_split 170 171 (by norm_num) (by norm_num) rows225C_1191 c170_3 (by norm_num)

theorem c170_1 : rowsJ 170 171 54 400 ≤ 1308813464148819 :=
  rowsJ_le_of_split 170 171 (by norm_num) (by norm_num) rows225C_1190 c170_2 (by norm_num)

theorem c170_0 : rowsJ 170 171 0 400 ≤ 1354543242878275 :=
  rowsJ_le_of_split 170 171 (by norm_num) (by norm_num) rows225C_1189 c170_1 (by norm_num)

theorem hr170 : rows 170 171 ≤ 1354543242878275 := rows_le_of_rowsJ 170 171 c170_0

theorem c171_4 : rowsJ 171 172 70 400 ≤ 1335942577007107 :=
  rowsJ_le_of_split 171 172 (by norm_num) (by norm_num) rows225C_1199 rows225C_1200 (by norm_num)

theorem c171_3 : rowsJ 171 172 64 400 ≤ 1349199951125446 :=
  rowsJ_le_of_split 171 172 (by norm_num) (by norm_num) rows225C_1198 c171_4 (by norm_num)

theorem c171_2 : rowsJ 171 172 59 400 ≤ 1373410254629363 :=
  rowsJ_le_of_split 171 172 (by norm_num) (by norm_num) rows225C_1197 c171_3 (by norm_num)

theorem c171_1 : rowsJ 171 172 53 400 ≤ 1402058466819463 :=
  rowsJ_le_of_split 171 172 (by norm_num) (by norm_num) rows225C_1196 c171_2 (by norm_num)

theorem c171_0 : rowsJ 171 172 0 400 ≤ 1443690477462916 :=
  rowsJ_le_of_split 171 172 (by norm_num) (by norm_num) rows225C_1195 c171_1 (by norm_num)

theorem hr171 : rows 171 172 ≤ 1443690477462916 := rows_le_of_rowsJ 171 172 c171_0

theorem c172_4 : rowsJ 172 173 69 400 ≤ 1432464020267852 :=
  rowsJ_le_of_split 172 173 (by norm_num) (by norm_num) rows225C_1205 rows225C_1206 (by norm_num)

theorem c172_3 : rowsJ 172 173 63 400 ≤ 1447067524932307 :=
  rowsJ_le_of_split 172 173 (by norm_num) (by norm_num) rows225C_1204 c172_4 (by norm_num)

theorem c172_2 : rowsJ 172 173 58 400 ≤ 1473098619200250 :=
  rowsJ_le_of_split 172 173 (by norm_num) (by norm_num) rows225C_1203 c172_3 (by norm_num)

theorem c172_1 : rowsJ 172 173 53 400 ≤ 1497233538676093 :=
  rowsJ_le_of_split 172 173 (by norm_num) (by norm_num) rows225C_1202 c172_2 (by norm_num)

theorem c172_0 : rowsJ 172 173 0 400 ≤ 1537682742431627 :=
  rowsJ_le_of_split 172 173 (by norm_num) (by norm_num) rows225C_1201 c172_1 (by norm_num)

theorem hr172 : rows 172 173 ≤ 1537682742431627 := rows_le_of_rowsJ 172 173 c172_0

theorem c173_4 : rowsJ 173 174 69 400 ≤ 1527661633438585 :=
  rowsJ_le_of_split 173 174 (by norm_num) (by norm_num) rows225C_1211 rows225C_1212 (by norm_num)

theorem c173_3 : rowsJ 173 174 63 400 ≤ 1541290017183825 :=
  rowsJ_le_of_split 173 174 (by norm_num) (by norm_num) rows225C_1210 c173_4 (by norm_num)

theorem c173_2 : rowsJ 173 174 58 400 ≤ 1566182721338121 :=
  rowsJ_le_of_split 173 174 (by norm_num) (by norm_num) rows225C_1209 c173_3 (by norm_num)

theorem c173_1 : rowsJ 173 174 52 400 ≤ 1595648458072999 :=
  rowsJ_le_of_split 173 174 (by norm_num) (by norm_num) rows225C_1208 c173_2 (by norm_num)

theorem c173_0 : rowsJ 173 174 0 400 ≤ 1632258425781022 :=
  rowsJ_le_of_split 173 174 (by norm_num) (by norm_num) rows225C_1207 c173_1 (by norm_num)

theorem hr173 : rows 173 174 ≤ 1632258425781022 := rows_le_of_rowsJ 173 174 c173_0

theorem c174_4 : rowsJ 174 175 69 400 ≤ 1617469993010141 :=
  rowsJ_le_of_split 174 175 (by norm_num) (by norm_num) rows225C_1217 rows225C_1218 (by norm_num)

theorem c174_3 : rowsJ 174 175 63 400 ≤ 1630094964030236 :=
  rowsJ_le_of_split 174 175 (by norm_num) (by norm_num) rows225C_1216 c174_4 (by norm_num)

theorem c174_2 : rowsJ 174 175 58 400 ≤ 1653817086861248 :=
  rowsJ_le_of_split 174 175 (by norm_num) (by norm_num) rows225C_1215 c174_3 (by norm_num)

theorem c174_1 : rowsJ 174 175 52 400 ≤ 1685300519709985 :=
  rowsJ_le_of_split 174 175 (by norm_num) (by norm_num) rows225C_1214 c174_2 (by norm_num)

theorem c174_0 : rowsJ 174 175 0 400 ≤ 1721187860419854 :=
  rowsJ_le_of_split 174 175 (by norm_num) (by norm_num) rows225C_1213 c174_1 (by norm_num)

theorem hr174 : rows 174 175 ≤ 1721187860419854 := rows_le_of_rowsJ 174 175 c174_0

theorem c175_3 : rowsJ 175 176 64 400 ≤ 1721412824389221 :=
  rowsJ_le_of_split 175 176 (by norm_num) (by norm_num) rows225C_1222 rows225C_1223 (by norm_num)

theorem c175_2 : rowsJ 175 176 58 400 ≤ 1746955423608032 :=
  rowsJ_le_of_split 175 176 (by norm_num) (by norm_num) rows225C_1221 c175_3 (by norm_num)

theorem c175_1 : rowsJ 175 176 52 400 ≤ 1779940679514200 :=
  rowsJ_le_of_split 175 176 (by norm_num) (by norm_num) rows225C_1220 c175_2 (by norm_num)

theorem c175_0 : rowsJ 175 176 0 400 ≤ 1816007517351280 :=
  rowsJ_le_of_split 175 176 (by norm_num) (by norm_num) rows225C_1219 c175_1 (by norm_num)

theorem hr175 : rows 175 176 ≤ 1816007517351280 := rows_le_of_rowsJ 175 176 c175_0

theorem c176_3 : rowsJ 176 177 63 400 ≤ 1818440473606551 :=
  rowsJ_le_of_split 176 177 (by norm_num) (by norm_num) rows225C_1227 rows225C_1228 (by norm_num)

theorem c176_2 : rowsJ 176 177 57 400 ≤ 1846049420741235 :=
  rowsJ_le_of_split 176 177 (by norm_num) (by norm_num) rows225C_1226 c176_3 (by norm_num)

theorem c176_1 : rowsJ 176 177 51 400 ≤ 1878449991089360 :=
  rowsJ_le_of_split 176 177 (by norm_num) (by norm_num) rows225C_1225 c176_2 (by norm_num)

theorem c176_0 : rowsJ 176 177 0 400 ≤ 1910441810061175 :=
  rowsJ_le_of_split 176 177 (by norm_num) (by norm_num) rows225C_1224 c176_1 (by norm_num)

theorem hr176 : rows 176 177 ≤ 1910441810061175 := rows_le_of_rowsJ 176 177 c176_0

theorem c177_3 : rowsJ 177 178 63 400 ≤ 1824152706246222 :=
  rowsJ_le_of_split 177 178 (by norm_num) (by norm_num) rows225C_1232 rows225C_1233 (by norm_num)

theorem c177_2 : rowsJ 177 178 57 400 ≤ 1850435192725992 :=
  rowsJ_le_of_split 177 178 (by norm_num) (by norm_num) rows225C_1231 c177_3 (by norm_num)

theorem c177_1 : rowsJ 177 178 51 400 ≤ 1884387217790055 :=
  rowsJ_le_of_split 177 178 (by norm_num) (by norm_num) rows225C_1230 c177_2 (by norm_num)

theorem c177_0 : rowsJ 177 178 0 400 ≤ 1916985359704602 :=
  rowsJ_le_of_split 177 178 (by norm_num) (by norm_num) rows225C_1229 c177_1 (by norm_num)

theorem hr177 : rows 177 178 ≤ 1916985359704602 := rows_le_of_rowsJ 177 178 c177_0

theorem c178_3 : rowsJ 178 179 63 400 ≤ 1835391516544612 :=
  rowsJ_le_of_split 178 179 (by norm_num) (by norm_num) rows225C_1237 rows225C_1238 (by norm_num)

theorem c178_2 : rowsJ 178 179 57 400 ≤ 1860308506050100 :=
  rowsJ_le_of_split 178 179 (by norm_num) (by norm_num) rows225C_1236 c178_3 (by norm_num)

theorem c178_1 : rowsJ 178 179 51 400 ≤ 1895831298940596 :=
  rowsJ_le_of_split 178 179 (by norm_num) (by norm_num) rows225C_1235 c178_2 (by norm_num)

theorem c178_0 : rowsJ 178 179 0 400 ≤ 1928808951379928 :=
  rowsJ_le_of_split 178 179 (by norm_num) (by norm_num) rows225C_1234 c178_1 (by norm_num)

theorem hr178 : rows 178 179 ≤ 1928808951379928 := rows_le_of_rowsJ 178 179 c178_0

theorem c179_3 : rowsJ 179 180 62 400 ≤ 1849682941015545 :=
  rowsJ_le_of_split 179 180 (by norm_num) (by norm_num) rows225C_1242 rows225C_1243 (by norm_num)

theorem c179_2 : rowsJ 179 180 56 400 ≤ 1876738022310886 :=
  rowsJ_le_of_split 179 180 (by norm_num) (by norm_num) rows225C_1241 c179_3 (by norm_num)

theorem c179_1 : rowsJ 179 180 50 400 ≤ 1911699939628532 :=
  rowsJ_le_of_split 179 180 (by norm_num) (by norm_num) rows225C_1240 c179_2 (by norm_num)

theorem c179_0 : rowsJ 179 180 0 400 ≤ 1941471785124995 :=
  rowsJ_le_of_split 179 180 (by norm_num) (by norm_num) rows225C_1239 c179_1 (by norm_num)

theorem hr179 : rows 179 180 ≤ 1941471785124995 := rows_le_of_rowsJ 179 180 c179_0

theorem c180_3 : rowsJ 180 181 62 400 ≤ 1856155150635513 :=
  rowsJ_le_of_split 180 181 (by norm_num) (by norm_num) rows225C_1247 rows225C_1248 (by norm_num)

theorem c180_2 : rowsJ 180 181 56 400 ≤ 1881809414186089 :=
  rowsJ_le_of_split 180 181 (by norm_num) (by norm_num) rows225C_1246 c180_3 (by norm_num)

theorem c180_1 : rowsJ 180 181 50 400 ≤ 1918395234639812 :=
  rowsJ_le_of_split 180 181 (by norm_num) (by norm_num) rows225C_1245 c180_2 (by norm_num)

theorem c180_0 : rowsJ 180 181 0 400 ≤ 1949007810817910 :=
  rowsJ_le_of_split 180 181 (by norm_num) (by norm_num) rows225C_1244 c180_1 (by norm_num)

theorem hr180 : rows 180 181 ≤ 1949007810817910 := rows_le_of_rowsJ 180 181 c180_0

theorem c181_3 : rowsJ 181 182 61 400 ≤ 1871084754619397 :=
  rowsJ_le_of_split 181 182 (by norm_num) (by norm_num) rows225C_1252 rows225C_1253 (by norm_num)

theorem c181_2 : rowsJ 181 182 55 400 ≤ 1898946910102523 :=
  rowsJ_le_of_split 181 182 (by norm_num) (by norm_num) rows225C_1251 c181_3 (by norm_num)

theorem c181_1 : rowsJ 181 182 49 400 ≤ 1934964201858235 :=
  rowsJ_le_of_split 181 182 (by norm_num) (by norm_num) rows225C_1250 c181_2 (by norm_num)

theorem c181_0 : rowsJ 181 182 0 400 ≤ 1962615298577447 :=
  rowsJ_le_of_split 181 182 (by norm_num) (by norm_num) rows225C_1249 c181_1 (by norm_num)

theorem hr181 : rows 181 182 ≤ 1962615298577447 := rows_le_of_rowsJ 181 182 c181_0

theorem c182_3 : rowsJ 182 183 61 400 ≤ 1883317104657059 :=
  rowsJ_le_of_split 182 183 (by norm_num) (by norm_num) rows225C_1257 rows225C_1258 (by norm_num)

theorem c182_2 : rowsJ 182 183 55 400 ≤ 1909741680607937 :=
  rowsJ_le_of_split 182 183 (by norm_num) (by norm_num) rows225C_1256 c182_3 (by norm_num)

theorem c182_1 : rowsJ 182 183 49 400 ≤ 1947438595843714 :=
  rowsJ_le_of_split 182 183 (by norm_num) (by norm_num) rows225C_1255 c182_2 (by norm_num)

theorem c182_0 : rowsJ 182 183 0 400 ≤ 1976300227950333 :=
  rowsJ_le_of_split 182 183 (by norm_num) (by norm_num) rows225C_1254 c182_1 (by norm_num)

theorem hr182 : rows 182 183 ≤ 1976300227950333 := rows_le_of_rowsJ 182 183 c182_0

theorem c183_2 : rowsJ 183 184 55 400 ≤ 1915865453213965 :=
  rowsJ_le_of_split 183 184 (by norm_num) (by norm_num) rows225C_1261 rows225C_1262 (by norm_num)

theorem c183_1 : rowsJ 183 184 49 400 ≤ 1954651340349907 :=
  rowsJ_le_of_split 183 184 (by norm_num) (by norm_num) rows225C_1260 c183_2 (by norm_num)

theorem c183_0 : rowsJ 183 184 0 400 ≤ 1985587197698421 :=
  rowsJ_le_of_split 183 184 (by norm_num) (by norm_num) rows225C_1259 c183_1 (by norm_num)

theorem hr183 : rows 183 184 ≤ 1985587197698421 := rows_le_of_rowsJ 183 184 c183_0

theorem c184_2 : rowsJ 184 185 54 400 ≤ 1933606250841849 :=
  rowsJ_le_of_split 184 185 (by norm_num) (by norm_num) rows225C_1265 rows225C_1266 (by norm_num)

theorem c184_1 : rowsJ 184 185 48 400 ≤ 1972465000106297 :=
  rowsJ_le_of_split 184 185 (by norm_num) (by norm_num) rows225C_1264 c184_2 (by norm_num)

theorem c184_0 : rowsJ 184 185 0 400 ≤ 2000251198488034 :=
  rowsJ_le_of_split 184 185 (by norm_num) (by norm_num) rows225C_1263 c184_1 (by norm_num)

theorem hr184 : rows 184 185 ≤ 2000251198488034 := rows_le_of_rowsJ 184 185 c184_0

theorem c185_2 : rowsJ 185 186 54 400 ≤ 1945421255413492 :=
  rowsJ_le_of_split 185 186 (by norm_num) (by norm_num) rows225C_1269 rows225C_1270 (by norm_num)

theorem c185_1 : rowsJ 185 186 48 400 ≤ 1985410025685340 :=
  rowsJ_le_of_split 185 186 (by norm_num) (by norm_num) rows225C_1268 c185_2 (by norm_num)

theorem c185_0 : rowsJ 185 186 0 400 ≤ 2015556246730370 :=
  rowsJ_le_of_split 185 186 (by norm_num) (by norm_num) rows225C_1267 c185_1 (by norm_num)

theorem hr185 : rows 185 186 ≤ 2015556246730370 := rows_le_of_rowsJ 185 186 c185_0

theorem c186_2 : rowsJ 186 187 53 400 ≤ 1958592982758522 :=
  rowsJ_le_of_split 186 187 (by norm_num) (by norm_num) rows225C_1273 rows225C_1274 (by norm_num)

theorem c186_1 : rowsJ 186 187 47 400 ≤ 1998667157937150 :=
  rowsJ_le_of_split 186 187 (by norm_num) (by norm_num) rows225C_1272 c186_2 (by norm_num)

theorem c186_0 : rowsJ 186 187 0 400 ≤ 2025953358250919 :=
  rowsJ_le_of_split 186 187 (by norm_num) (by norm_num) rows225C_1271 c186_1 (by norm_num)

theorem hr186 : rows 186 187 ≤ 2025953358250919 := rows_le_of_rowsJ 186 187 c186_0

theorem c187_2 : rowsJ 187 188 53 400 ≤ 1970909519744159 :=
  rowsJ_le_of_split 187 188 (by norm_num) (by norm_num) rows225C_1277 rows225C_1278 (by norm_num)

theorem c187_1 : rowsJ 187 188 47 400 ≤ 2012156895683153 :=
  rowsJ_le_of_split 187 188 (by norm_num) (by norm_num) rows225C_1276 c187_2 (by norm_num)

theorem c187_0 : rowsJ 187 188 0 400 ≤ 2042115743650550 :=
  rowsJ_le_of_split 187 188 (by norm_num) (by norm_num) rows225C_1275 c187_1 (by norm_num)

theorem hr187 : rows 187 188 ≤ 2042115743650550 := rows_le_of_rowsJ 187 188 c187_0

theorem c188_2 : rowsJ 188 189 53 400 ≤ 1983405375572117 :=
  rowsJ_le_of_split 188 189 (by norm_num) (by norm_num) rows225C_1281 rows225C_1282 (by norm_num)

theorem c188_1 : rowsJ 188 189 47 400 ≤ 2025836609087672 :=
  rowsJ_le_of_split 188 189 (by norm_num) (by norm_num) rows225C_1280 c188_2 (by norm_num)

theorem c188_0 : rowsJ 188 189 0 400 ≤ 2058538898111278 :=
  rowsJ_le_of_split 188 189 (by norm_num) (by norm_num) rows225C_1279 c188_1 (by norm_num)

theorem hr188 : rows 188 189 ≤ 2058538898111278 := rows_le_of_rowsJ 188 189 c188_0

theorem c189_2 : rowsJ 189 190 53 400 ≤ 1991232554707795 :=
  rowsJ_le_of_split 189 190 (by norm_num) (by norm_num) rows225C_1285 rows225C_1286 (by norm_num)

theorem c189_1 : rowsJ 189 190 46 400 ≤ 2040059407251125 :=
  rowsJ_le_of_split 189 190 (by norm_num) (by norm_num) rows225C_1284 c189_2 (by norm_num)

theorem c189_0 : rowsJ 189 190 0 400 ≤ 2070318626618420 :=
  rowsJ_le_of_split 189 190 (by norm_num) (by norm_num) rows225C_1283 c189_1 (by norm_num)

theorem hr189 : rows 189 190 ≤ 2070318626618420 := rows_le_of_rowsJ 189 190 c189_0

theorem c190_2 : rowsJ 190 191 53 400 ≤ 2004508084820091 :=
  rowsJ_le_of_split 190 191 (by norm_num) (by norm_num) rows225C_1289 rows225C_1290 (by norm_num)

theorem c190_1 : rowsJ 190 191 46 400 ≤ 2054277009102062 :=
  rowsJ_le_of_split 190 191 (by norm_num) (by norm_num) rows225C_1288 c190_2 (by norm_num)

theorem c190_0 : rowsJ 190 191 0 400 ≤ 2087624568448109 :=
  rowsJ_le_of_split 190 191 (by norm_num) (by norm_num) rows225C_1287 c190_1 (by norm_num)

theorem hr190 : rows 190 191 ≤ 2087624568448109 := rows_le_of_rowsJ 190 191 c190_0

theorem c191_2 : rowsJ 191 192 53 400 ≤ 2018232692744327 :=
  rowsJ_le_of_split 191 192 (by norm_num) (by norm_num) rows225C_1293 rows225C_1294 (by norm_num)

theorem c191_1 : rowsJ 191 192 46 400 ≤ 2068276063455453 :=
  rowsJ_le_of_split 191 192 (by norm_num) (by norm_num) rows225C_1292 c191_2 (by norm_num)

theorem c191_0 : rowsJ 191 192 0 400 ≤ 2105256991704564 :=
  rowsJ_le_of_split 191 192 (by norm_num) (by norm_num) rows225C_1291 c191_1 (by norm_num)

theorem hr191 : rows 191 192 ≤ 2105256991704564 := rows_le_of_rowsJ 191 192 c191_0

theorem c192_2 : rowsJ 192 193 52 400 ≤ 2032452538762161 :=
  rowsJ_le_of_split 192 193 (by norm_num) (by norm_num) rows225C_1297 rows225C_1298 (by norm_num)

theorem c192_1 : rowsJ 192 193 45 400 ≤ 2083843389476674 :=
  rowsJ_le_of_split 192 193 (by norm_num) (by norm_num) rows225C_1296 c192_2 (by norm_num)

theorem c192_0 : rowsJ 192 193 0 400 ≤ 2118067114129802 :=
  rowsJ_le_of_split 192 193 (by norm_num) (by norm_num) rows225C_1295 c192_1 (by norm_num)

theorem hr192 : rows 192 193 ≤ 2118067114129802 := rows_le_of_rowsJ 192 193 c192_0

theorem c193_1 : rowsJ 193 194 45 400 ≤ 2098333246559564 :=
  rowsJ_le_of_split 193 194 (by norm_num) (by norm_num) rows225C_1300 rows225C_1301 (by norm_num)

theorem c193_0 : rowsJ 193 194 0 400 ≤ 2136255753406777 :=
  rowsJ_le_of_split 193 194 (by norm_num) (by norm_num) rows225C_1299 c193_1 (by norm_num)

theorem hr193 : rows 193 194 ≤ 2136255753406777 := rows_le_of_rowsJ 193 194 c193_0

theorem c194_1 : rowsJ 194 195 44 400 ≤ 2114511365950087 :=
  rowsJ_le_of_split 194 195 (by norm_num) (by norm_num) rows225C_1303 rows225C_1304 (by norm_num)

theorem c194_0 : rowsJ 194 195 0 400 ≤ 2149528867643625 :=
  rowsJ_le_of_split 194 195 (by norm_num) (by norm_num) rows225C_1302 c194_1 (by norm_num)

theorem hr194 : rows 194 195 ≤ 2149528867643625 := rows_le_of_rowsJ 194 195 c194_0

theorem c195_1 : rowsJ 195 196 44 400 ≤ 2124033466170230 :=
  rowsJ_le_of_split 195 196 (by norm_num) (by norm_num) rows225C_1306 rows225C_1307 (by norm_num)

theorem c195_0 : rowsJ 195 196 0 400 ≤ 2162815535743195 :=
  rowsJ_le_of_split 195 196 (by norm_num) (by norm_num) rows225C_1305 c195_1 (by norm_num)

theorem hr195 : rows 195 196 ≤ 2162815535743195 := rows_le_of_rowsJ 195 196 c195_0

theorem c196_1 : rowsJ 196 197 44 400 ≤ 2133644544307991 :=
  rowsJ_le_of_split 196 197 (by norm_num) (by norm_num) rows225C_1309 rows225C_1310 (by norm_num)

theorem c196_0 : rowsJ 196 197 0 400 ≤ 2176313563990889 :=
  rowsJ_le_of_split 196 197 (by norm_num) (by norm_num) rows225C_1308 c196_1 (by norm_num)

theorem hr196 : rows 196 197 ≤ 2176313563990889 := rows_le_of_rowsJ 196 197 c196_0

theorem c197_1 : rowsJ 197 198 43 400 ≤ 2150244175050578 :=
  rowsJ_le_of_split 197 198 (by norm_num) (by norm_num) rows225C_1312 rows225C_1313 (by norm_num)

theorem c197_0 : rowsJ 197 198 0 400 ≤ 2189763297830075 :=
  rowsJ_le_of_split 197 198 (by norm_num) (by norm_num) rows225C_1311 c197_1 (by norm_num)

theorem hr197 : rows 197 198 ≤ 2189763297830075 := rows_le_of_rowsJ 197 198 c197_0

theorem c198_1 : rowsJ 198 199 43 400 ≤ 2159978278599889 :=
  rowsJ_le_of_split 198 199 (by norm_num) (by norm_num) rows225C_1315 rows225C_1316 (by norm_num)

theorem c198_0 : rowsJ 198 199 0 400 ≤ 2203453632525121 :=
  rowsJ_le_of_split 198 199 (by norm_num) (by norm_num) rows225C_1314 c198_1 (by norm_num)

theorem hr198 : rows 198 199 ≤ 2203453632525121 := rows_le_of_rowsJ 198 199 c198_0

theorem c199_1 : rowsJ 199 200 43 400 ≤ 2169191988083686 :=
  rowsJ_le_of_split 199 200 (by norm_num) (by norm_num) rows225C_1318 rows225C_1319 (by norm_num)

theorem c199_0 : rowsJ 199 200 0 400 ≤ 2217028238337075 :=
  rowsJ_le_of_split 199 200 (by norm_num) (by norm_num) rows225C_1317 c199_1 (by norm_num)

theorem hr199 : rows 199 200 ≤ 2217028238337075 := rows_le_of_rowsJ 199 200 c199_0

theorem c200_1 : rowsJ 200 201 42 400 ≤ 2186728427279037 :=
  rowsJ_le_of_split 200 201 (by norm_num) (by norm_num) rows225C_1321 rows225C_1322 (by norm_num)

theorem c200_0 : rowsJ 200 201 0 400 ≤ 2230841363307783 :=
  rowsJ_le_of_split 200 201 (by norm_num) (by norm_num) rows225C_1320 c200_1 (by norm_num)

theorem hr200 : rows 200 201 ≤ 2230841363307783 := rows_le_of_rowsJ 200 201 c200_0

theorem c201_1 : rowsJ 201 202 42 400 ≤ 2195973023134605 :=
  rowsJ_le_of_split 201 202 (by norm_num) (by norm_num) rows225C_1324 rows225C_1325 (by norm_num)

theorem c201_0 : rowsJ 201 202 0 400 ≤ 2244496083785339 :=
  rowsJ_le_of_split 201 202 (by norm_num) (by norm_num) rows225C_1323 c201_1 (by norm_num)

theorem hr201 : rows 201 202 ≤ 2244496083785339 := rows_le_of_rowsJ 201 202 c201_0

theorem c202_1 : rowsJ 202 203 42 400 ≤ 2205276956155864 :=
  rowsJ_le_of_split 202 203 (by norm_num) (by norm_num) rows225C_1327 rows225C_1328 (by norm_num)

theorem c202_0 : rowsJ 202 203 0 400 ≤ 2258385273421247 :=
  rowsJ_le_of_split 202 203 (by norm_num) (by norm_num) rows225C_1326 c202_1 (by norm_num)

theorem hr202 : rows 202 203 ≤ 2258385273421247 := rows_le_of_rowsJ 202 203 c202_0

theorem c203_1 : rowsJ 203 204 41 400 ≤ 2223049748383600 :=
  rowsJ_le_of_split 203 204 (by norm_num) (by norm_num) rows225C_1330 rows225C_1331 (by norm_num)

theorem c203_0 : rowsJ 203 204 0 400 ≤ 2272035876143964 :=
  rowsJ_le_of_split 203 204 (by norm_num) (by norm_num) rows225C_1329 c203_1 (by norm_num)

theorem hr203 : rows 203 204 ≤ 2272035876143964 := rows_le_of_rowsJ 203 204 c203_0

theorem c204_0 : rowsJ 204 205 0 400 ≤ 2285946507032565 :=
  rowsJ_le_of_split 204 205 (by norm_num) (by norm_num) rows225C_1332 rows225C_1333 (by norm_num)

theorem hr204 : rows 204 205 ≤ 2285946507032565 := rows_le_of_rowsJ 204 205 c204_0

theorem c205_0 : rowsJ 205 206 0 400 ≤ 2299530709493073 :=
  rowsJ_le_of_split 205 206 (by norm_num) (by norm_num) rows225C_1334 rows225C_1335 (by norm_num)

theorem hr205 : rows 205 206 ≤ 2299530709493073 := rows_le_of_rowsJ 205 206 c205_0

theorem c206_0 : rowsJ 206 207 0 400 ≤ 2313366085762653 :=
  rowsJ_le_of_split 206 207 (by norm_num) (by norm_num) rows225C_1336 rows225C_1337 (by norm_num)

theorem hr206 : rows 206 207 ≤ 2313366085762653 := rows_le_of_rowsJ 206 207 c206_0

theorem c207_0 : rowsJ 207 208 0 400 ≤ 2326811672850976 :=
  rowsJ_le_of_split 207 208 (by norm_num) (by norm_num) rows225C_1338 rows225C_1339 (by norm_num)

theorem hr207 : rows 207 208 ≤ 2326811672850976 := rows_le_of_rowsJ 207 208 c207_0

theorem c208_0 : rowsJ 208 209 0 400 ≤ 2378446387246976 :=
  rowsJ_le_of_split 208 209 (by norm_num) (by norm_num) rows225C_1340 rows225C_1341 (by norm_num)

theorem hr208 : rows 208 209 ≤ 2378446387246976 := rows_le_of_rowsJ 208 209 c208_0

theorem c209_0 : rowsJ 209 210 0 400 ≤ 2467418053548306 :=
  rowsJ_le_of_split 209 210 (by norm_num) (by norm_num) rows225C_1342 rows225C_1343 (by norm_num)

theorem hr209 : rows 209 210 ≤ 2467418053548306 := rows_le_of_rowsJ 209 210 c209_0

theorem c210_0 : rowsJ 210 211 0 400 ≤ 2556495015349893 :=
  rowsJ_le_of_split 210 211 (by norm_num) (by norm_num) rows225C_1344 rows225C_1345 (by norm_num)

theorem hr210 : rows 210 211 ≤ 2556495015349893 := rows_le_of_rowsJ 210 211 c210_0

theorem c211_0 : rowsJ 211 212 0 400 ≤ 2644815166285816 :=
  rowsJ_le_of_split 211 212 (by norm_num) (by norm_num) rows225C_1346 rows225C_1347 (by norm_num)

theorem hr211 : rows 211 212 ≤ 2644815166285816 := rows_le_of_rowsJ 211 212 c211_0

theorem c212_0 : rowsJ 212 213 0 400 ≤ 2733233089210012 :=
  rowsJ_le_of_split 212 213 (by norm_num) (by norm_num) rows225C_1348 rows225C_1349 (by norm_num)

theorem hr212 : rows 212 213 ≤ 2733233089210012 := rows_le_of_rowsJ 212 213 c212_0

theorem c213_0 : rowsJ 213 214 0 400 ≤ 2820814144752625 :=
  rowsJ_le_of_split 213 214 (by norm_num) (by norm_num) rows225C_1350 rows225C_1351 (by norm_num)

theorem hr213 : rows 213 214 ≤ 2820814144752625 := rows_le_of_rowsJ 213 214 c213_0

theorem c214_0 : rowsJ 214 215 0 400 ≤ 2908479805106645 :=
  rowsJ_le_of_split 214 215 (by norm_num) (by norm_num) rows225C_1352 rows225C_1353 (by norm_num)

theorem hr214 : rows 214 215 ≤ 2908479805106645 := rows_le_of_rowsJ 214 215 c214_0

theorem c215_0 : rowsJ 215 216 0 400 ≤ 2995180077605833 :=
  rowsJ_le_of_split 215 216 (by norm_num) (by norm_num) rows225C_1354 rows225C_1355 (by norm_num)

theorem hr215 : rows 215 216 ≤ 2995180077605833 := rows_le_of_rowsJ 215 216 c215_0

theorem t209 : rows 313 400 ≤ 231046024027975403 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_1372 rows225C_1373 (by norm_num)

theorem t208 : rows 296 400 ≤ 375475135827116232 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_1371 t209 (by norm_num)

theorem t207 : rows 277 400 ≤ 533807307563869605 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_1370 t208 (by norm_num)

theorem t206 : rows 257 400 ≤ 675436459129273010 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_1369 t207 (by norm_num)

theorem t205 : rows 236 400 ≤ 796322882084768188 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_1368 t206 (by norm_num)

theorem t204 : rows 231 400 ≤ 819368051242681544 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_1367 t205 (by norm_num)

theorem t203 : rows 228 400 ≤ 832051140042665198 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_1366 t204 (by norm_num)

theorem t202 : rows 226 400 ≤ 840043890846784539 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_1365 t203 (by norm_num)

theorem t201 : rows 224 400 ≤ 847674986366308922 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_1364 t202 (by norm_num)

theorem t200 : rows 223 400 ≤ 851357262459249413 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_1363 t201 (by norm_num)

theorem t199 : rows 222 400 ≤ 854951980387289422 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_1362 t200 (by norm_num)

theorem t198 : rows 221 400 ≤ 858460108777416990 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_1361 t199 (by norm_num)

theorem t197 : rows 220 400 ≤ 861882600362984945 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_1360 t198 (by norm_num)

theorem t196 : rows 219 400 ≤ 865220408166256043 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_1359 t197 (by norm_num)

theorem t195 : rows 218 400 ≤ 868473629050312488 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_1358 t196 (by norm_num)

theorem t194 : rows 217 400 ≤ 871641195112979570 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_1357 t195 (by norm_num)

theorem t193 : rows 216 400 ≤ 874723123368562217 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_1356 t194 (by norm_num)

theorem t192 : rows 215 400 ≤ 877718303446168050 :=
  rows_le_of_split (by norm_num) (by norm_num) hr215 t193 (by norm_num)

theorem t191 : rows 214 400 ≤ 880626783251274695 :=
  rows_le_of_split (by norm_num) (by norm_num) hr214 t192 (by norm_num)

theorem t190 : rows 213 400 ≤ 883447597396027320 :=
  rows_le_of_split (by norm_num) (by norm_num) hr213 t191 (by norm_num)

theorem t189 : rows 212 400 ≤ 886180830485237332 :=
  rows_le_of_split (by norm_num) (by norm_num) hr212 t190 (by norm_num)

theorem t188 : rows 211 400 ≤ 888825645651523148 :=
  rows_le_of_split (by norm_num) (by norm_num) hr211 t189 (by norm_num)

theorem t187 : rows 210 400 ≤ 891382140666873041 :=
  rows_le_of_split (by norm_num) (by norm_num) hr210 t188 (by norm_num)

theorem t186 : rows 209 400 ≤ 893849558720421347 :=
  rows_le_of_split (by norm_num) (by norm_num) hr209 t187 (by norm_num)

theorem t185 : rows 208 400 ≤ 896228005107668323 :=
  rows_le_of_split (by norm_num) (by norm_num) hr208 t186 (by norm_num)

theorem t184 : rows 207 400 ≤ 898554816780519299 :=
  rows_le_of_split (by norm_num) (by norm_num) hr207 t185 (by norm_num)

theorem t183 : rows 206 400 ≤ 900868182866281952 :=
  rows_le_of_split (by norm_num) (by norm_num) hr206 t184 (by norm_num)

theorem t182 : rows 205 400 ≤ 903167713575775025 :=
  rows_le_of_split (by norm_num) (by norm_num) hr205 t183 (by norm_num)

theorem t181 : rows 204 400 ≤ 905453660082807590 :=
  rows_le_of_split (by norm_num) (by norm_num) hr204 t182 (by norm_num)

theorem t180 : rows 203 400 ≤ 907725695958951554 :=
  rows_le_of_split (by norm_num) (by norm_num) hr203 t181 (by norm_num)

theorem t179 : rows 202 400 ≤ 909984081232372801 :=
  rows_le_of_split (by norm_num) (by norm_num) hr202 t180 (by norm_num)

theorem t178 : rows 201 400 ≤ 912228577316158140 :=
  rows_le_of_split (by norm_num) (by norm_num) hr201 t179 (by norm_num)

theorem t177 : rows 200 400 ≤ 914459418679465923 :=
  rows_le_of_split (by norm_num) (by norm_num) hr200 t178 (by norm_num)

theorem t176 : rows 199 400 ≤ 916676446917802998 :=
  rows_le_of_split (by norm_num) (by norm_num) hr199 t177 (by norm_num)

theorem t175 : rows 198 400 ≤ 918879900550328119 :=
  rows_le_of_split (by norm_num) (by norm_num) hr198 t176 (by norm_num)

theorem t174 : rows 197 400 ≤ 921069663848158194 :=
  rows_le_of_split (by norm_num) (by norm_num) hr197 t175 (by norm_num)

theorem t173 : rows 196 400 ≤ 923245977412149083 :=
  rows_le_of_split (by norm_num) (by norm_num) hr196 t174 (by norm_num)

theorem t172 : rows 195 400 ≤ 925408792947892278 :=
  rows_le_of_split (by norm_num) (by norm_num) hr195 t173 (by norm_num)

theorem t171 : rows 194 400 ≤ 927558321815535903 :=
  rows_le_of_split (by norm_num) (by norm_num) hr194 t172 (by norm_num)

theorem t170 : rows 193 400 ≤ 929694577568942680 :=
  rows_le_of_split (by norm_num) (by norm_num) hr193 t171 (by norm_num)

theorem t169 : rows 192 400 ≤ 931812644683072482 :=
  rows_le_of_split (by norm_num) (by norm_num) hr192 t170 (by norm_num)

theorem t168 : rows 191 400 ≤ 933917901674777046 :=
  rows_le_of_split (by norm_num) (by norm_num) hr191 t169 (by norm_num)

theorem t167 : rows 190 400 ≤ 936005526243225155 :=
  rows_le_of_split (by norm_num) (by norm_num) hr190 t168 (by norm_num)

theorem t166 : rows 189 400 ≤ 938075844869843575 :=
  rows_le_of_split (by norm_num) (by norm_num) hr189 t167 (by norm_num)

theorem t165 : rows 188 400 ≤ 940134383767954853 :=
  rows_le_of_split (by norm_num) (by norm_num) hr188 t166 (by norm_num)

theorem t164 : rows 187 400 ≤ 942176499511605403 :=
  rows_le_of_split (by norm_num) (by norm_num) hr187 t165 (by norm_num)

theorem t163 : rows 186 400 ≤ 944202452869856322 :=
  rows_le_of_split (by norm_num) (by norm_num) hr186 t164 (by norm_num)

theorem t162 : rows 185 400 ≤ 946218009116586692 :=
  rows_le_of_split (by norm_num) (by norm_num) hr185 t163 (by norm_num)

theorem t161 : rows 184 400 ≤ 948218260315074726 :=
  rows_le_of_split (by norm_num) (by norm_num) hr184 t162 (by norm_num)

theorem t160 : rows 183 400 ≤ 950203847512773147 :=
  rows_le_of_split (by norm_num) (by norm_num) hr183 t161 (by norm_num)

theorem t159 : rows 182 400 ≤ 952180147740723480 :=
  rows_le_of_split (by norm_num) (by norm_num) hr182 t160 (by norm_num)

theorem t158 : rows 181 400 ≤ 954142763039300927 :=
  rows_le_of_split (by norm_num) (by norm_num) hr181 t159 (by norm_num)

theorem t157 : rows 180 400 ≤ 956091770850118837 :=
  rows_le_of_split (by norm_num) (by norm_num) hr180 t158 (by norm_num)

theorem t156 : rows 179 400 ≤ 958033242635243832 :=
  rows_le_of_split (by norm_num) (by norm_num) hr179 t157 (by norm_num)

theorem t155 : rows 178 400 ≤ 959962051586623760 :=
  rows_le_of_split (by norm_num) (by norm_num) hr178 t156 (by norm_num)

theorem t154 : rows 177 400 ≤ 961879036946328362 :=
  rows_le_of_split (by norm_num) (by norm_num) hr177 t155 (by norm_num)

theorem t153 : rows 176 400 ≤ 963789478756389537 :=
  rows_le_of_split (by norm_num) (by norm_num) hr176 t154 (by norm_num)

theorem t152 : rows 175 400 ≤ 965605486273740817 :=
  rows_le_of_split (by norm_num) (by norm_num) hr175 t153 (by norm_num)

theorem t151 : rows 174 400 ≤ 967326674134160671 :=
  rows_le_of_split (by norm_num) (by norm_num) hr174 t152 (by norm_num)

theorem t150 : rows 173 400 ≤ 968958932559941693 :=
  rows_le_of_split (by norm_num) (by norm_num) hr173 t151 (by norm_num)

theorem t149 : rows 172 400 ≤ 970496615302373320 :=
  rows_le_of_split (by norm_num) (by norm_num) hr172 t150 (by norm_num)

theorem t148 : rows 171 400 ≤ 971940305779836236 :=
  rows_le_of_split (by norm_num) (by norm_num) hr171 t149 (by norm_num)

theorem t147 : rows 170 400 ≤ 973294849022714511 :=
  rows_le_of_split (by norm_num) (by norm_num) hr170 t148 (by norm_num)

theorem t146 : rows 169 400 ≤ 974555609663314558 :=
  rows_le_of_split (by norm_num) (by norm_num) hr169 t147 (by norm_num)

theorem t145 : rows 168 400 ≤ 975722034616281557 :=
  rows_le_of_split (by norm_num) (by norm_num) hr168 t146 (by norm_num)

theorem t144 : rows 167 400 ≤ 976794687235855829 :=
  rows_le_of_split (by norm_num) (by norm_num) hr167 t145 (by norm_num)

theorem t143 : rows 166 400 ≤ 977767145549924457 :=
  rows_le_of_split (by norm_num) (by norm_num) hr166 t144 (by norm_num)

theorem t142 : rows 165 400 ≤ 978639438981908705 :=
  rows_le_of_split (by norm_num) (by norm_num) hr165 t143 (by norm_num)

theorem t141 : rows 164 400 ≤ 979410292695491612 :=
  rows_le_of_split (by norm_num) (by norm_num) hr164 t142 (by norm_num)

theorem t140 : rows 163 400 ≤ 980079748991077041 :=
  rows_le_of_split (by norm_num) (by norm_num) hr163 t141 (by norm_num)

theorem t139 : rows 162 400 ≤ 980646493969967384 :=
  rows_le_of_split (by norm_num) (by norm_num) hr162 t140 (by norm_num)

theorem t138 : rows 161 400 ≤ 981110469221525732 :=
  rows_le_of_split (by norm_num) (by norm_num) hr161 t139 (by norm_num)

theorem t137 : rows 160 400 ≤ 981470269313278829 :=
  rows_le_of_split (by norm_num) (by norm_num) hr160 t138 (by norm_num)

theorem t136 : rows 159 400 ≤ 981725808817709695 :=
  rows_le_of_split (by norm_num) (by norm_num) hr159 t137 (by norm_num)

theorem t135 : rows 158 400 ≤ 981875482743131885 :=
  rows_le_of_split (by norm_num) (by norm_num) hr158 t136 (by norm_num)

theorem t134 : rows 157 400 ≤ 982030316947464988 :=
  rows_le_of_split (by norm_num) (by norm_num) hr157 t135 (by norm_num)

theorem t133 : rows 156 400 ≤ 982294832732812577 :=
  rows_le_of_split (by norm_num) (by norm_num) hr156 t134 (by norm_num)

theorem t132 : rows 155 400 ≤ 982564458289585711 :=
  rows_le_of_split (by norm_num) (by norm_num) hr155 t133 (by norm_num)

theorem t131 : rows 154 400 ≤ 982942638596557607 :=
  rows_le_of_split (by norm_num) (by norm_num) hr154 t132 (by norm_num)

theorem t130 : rows 153 400 ≤ 983325794129591008 :=
  rows_le_of_split (by norm_num) (by norm_num) hr153 t131 (by norm_num)

theorem t129 : rows 152 400 ≤ 983816138753801515 :=
  rows_le_of_split (by norm_num) (by norm_num) hr152 t130 (by norm_num)

theorem t128 : rows 151 400 ≤ 984311110862506474 :=
  rows_le_of_split (by norm_num) (by norm_num) hr151 t129 (by norm_num)

theorem t127 : rows 150 400 ≤ 984911995614971220 :=
  rows_le_of_split (by norm_num) (by norm_num) hr150 t128 (by norm_num)

theorem t126 : rows 149 400 ≤ 985516991225239259 :=
  rows_le_of_split (by norm_num) (by norm_num) hr149 t127 (by norm_num)

theorem t125 : rows 148 400 ≤ 986226564269508917 :=
  rows_le_of_split (by norm_num) (by norm_num) hr148 t126 (by norm_num)

theorem t124 : rows 147 400 ≤ 986939829063762238 :=
  rows_le_of_split (by norm_num) (by norm_num) hr147 t125 (by norm_num)

theorem t123 : rows 146 400 ≤ 987756555009991425 :=
  rows_le_of_split (by norm_num) (by norm_num) hr146 t124 (by norm_num)

theorem t122 : rows 145 400 ≤ 988576721783433846 :=
  rows_le_of_split (by norm_num) (by norm_num) hr145 t123 (by norm_num)

theorem t121 : rows 144 400 ≤ 989499530501154926 :=
  rows_le_of_split (by norm_num) (by norm_num) hr144 t122 (by norm_num)

theorem t120 : rows 143 400 ≤ 990425707904577956 :=
  rows_le_of_split (by norm_num) (by norm_num) hr143 t121 (by norm_num)

theorem t119 : rows 142 400 ≤ 991453961843969849 :=
  rows_le_of_split (by norm_num) (by norm_num) hr142 t120 (by norm_num)

theorem t118 : rows 141 400 ≤ 992485777257703899 :=
  rows_le_of_split (by norm_num) (by norm_num) hr141 t119 (by norm_num)

theorem t117 : rows 140 400 ≤ 993619336561114101 :=
  rows_le_of_split (by norm_num) (by norm_num) hr140 t118 (by norm_num)

theorem t116 : rows 139 400 ≤ 994756848518576834 :=
  rows_le_of_split (by norm_num) (by norm_num) hr139 t117 (by norm_num)

theorem t115 : rows 138 400 ≤ 995996116374256807 :=
  rows_le_of_split (by norm_num) (by norm_num) hr138 t116 (by norm_num)

theorem t114 : rows 137 400 ≤ 997239939494561268 :=
  rows_le_of_split (by norm_num) (by norm_num) hr137 t115 (by norm_num)

theorem t113 : rows 136 400 ≤ 998585781431360776 :=
  rows_le_of_split (by norm_num) (by norm_num) hr136 t114 (by norm_num)

theorem t112 : rows 135 400 ≤ 999937002840317501 :=
  rows_le_of_split (by norm_num) (by norm_num) hr135 t113 (by norm_num)

theorem t111 : rows 134 400 ≤ 1001390576688352455 :=
  rows_le_of_split (by norm_num) (by norm_num) hr134 t112 (by norm_num)

theorem t110 : rows 133 400 ≤ 1002850221252525652 :=
  rows_le_of_split (by norm_num) (by norm_num) hr133 t111 (by norm_num)

theorem t109 : rows 132 400 ≤ 1004412495275492887 :=
  rows_le_of_split (by norm_num) (by norm_num) hr132 t110 (by norm_num)

theorem t108 : rows 131 400 ≤ 1005981380119689942 :=
  rows_le_of_split (by norm_num) (by norm_num) hr131 t109 (by norm_num)

theorem t107 : rows 130 400 ≤ 1007653080995604545 :=
  rows_le_of_split (by norm_num) (by norm_num) hr130 t108 (by norm_num)

theorem t106 : rows 129 400 ≤ 1009331856896267389 :=
  rows_le_of_split (by norm_num) (by norm_num) hr129 t107 (by norm_num)

theorem t105 : rows 128 400 ≤ 1011113525080236563 :=
  rows_le_of_split (by norm_num) (by norm_num) hr128 t106 (by norm_num)

theorem t104 : rows 127 400 ≤ 1012902597108034200 :=
  rows_le_of_split (by norm_num) (by norm_num) hr127 t105 (by norm_num)

theorem t103 : rows 126 400 ≤ 1014707489389527243 :=
  rows_le_of_split (by norm_num) (by norm_num) hr126 t104 (by norm_num)

theorem t102 : rows 125 400 ≤ 1016344321813040322 :=
  rows_le_of_split (by norm_num) (by norm_num) hr125 t103 (by norm_num)

theorem t101 : rows 124 400 ≤ 1017906687569921889 :=
  rows_le_of_split (by norm_num) (by norm_num) hr124 t102 (by norm_num)

theorem t100 : rows 123 400 ≤ 1019297446460108763 :=
  rows_le_of_split (by norm_num) (by norm_num) hr123 t101 (by norm_num)

theorem t99 : rows 122 400 ≤ 1020609832054281735 :=
  rows_le_of_split (by norm_num) (by norm_num) hr122 t100 (by norm_num)

theorem t98 : rows 121 400 ≤ 1021746948816877619 :=
  rows_le_of_split (by norm_num) (by norm_num) hr121 t99 (by norm_num)

theorem t97 : rows 120 400 ≤ 1022801795772668594 :=
  rows_le_of_split (by norm_num) (by norm_num) hr120 t98 (by norm_num)

theorem t96 : rows 119 400 ≤ 1023677483483380944 :=
  rows_le_of_split (by norm_num) (by norm_num) hr119 t97 (by norm_num)

theorem t95 : rows 118 400 ≤ 1024467032712442571 :=
  rows_le_of_split (by norm_num) (by norm_num) hr118 t96 (by norm_num)

theorem t94 : rows 117 400 ≤ 1025073534136182366 :=
  rows_le_of_split (by norm_num) (by norm_num) hr117 t95 (by norm_num)

theorem t93 : rows 116 400 ≤ 1025589847425758194 :=
  rows_le_of_split (by norm_num) (by norm_num) hr116 t94 (by norm_num)

theorem t92 : rows 115 400 ≤ 1026113627948105751 :=
  rows_le_of_split (by norm_num) (by norm_num) hr115 t93 (by norm_num)

theorem t91 : rows 114 400 ≤ 1026645863546160782 :=
  rows_le_of_split (by norm_num) (by norm_num) hr114 t92 (by norm_num)

theorem t90 : rows 113 400 ≤ 1027189436852439032 :=
  rows_le_of_split (by norm_num) (by norm_num) hr113 t91 (by norm_num)

theorem t89 : rows 112 400 ≤ 1027745327499613677 :=
  rows_le_of_split (by norm_num) (by norm_num) hr112 t90 (by norm_num)

theorem t88 : rows 111 400 ≤ 1028316176381826926 :=
  rows_le_of_split (by norm_num) (by norm_num) hr111 t89 (by norm_num)

theorem t87 : rows 110 400 ≤ 1028902808913442912 :=
  rows_le_of_split (by norm_num) (by norm_num) hr110 t88 (by norm_num)

theorem t86 : rows 109 400 ≤ 1029507812103164873 :=
  rows_le_of_split (by norm_num) (by norm_num) hr109 t87 (by norm_num)

theorem t85 : rows 108 400 ≤ 1030131903770820746 :=
  rows_le_of_split (by norm_num) (by norm_num) hr108 t86 (by norm_num)

theorem t84 : rows 107 400 ≤ 1030777383150359895 :=
  rows_le_of_split (by norm_num) (by norm_num) hr107 t85 (by norm_num)

theorem t83 : rows 106 400 ≤ 1031444783862568822 :=
  rows_le_of_split (by norm_num) (by norm_num) hr106 t84 (by norm_num)

theorem t82 : rows 105 400 ≤ 1032135898904868228 :=
  rows_le_of_split (by norm_num) (by norm_num) hr105 t83 (by norm_num)

theorem t81 : rows 104 400 ≤ 1032850824760366734 :=
  rows_le_of_split (by norm_num) (by norm_num) hr104 t82 (by norm_num)

theorem t80 : rows 103 400 ≤ 1033591015849231592 :=
  rows_le_of_split (by norm_num) (by norm_num) hr103 t81 (by norm_num)

theorem t79 : rows 102 400 ≤ 1034356230536029065 :=
  rows_le_of_split (by norm_num) (by norm_num) hr102 t80 (by norm_num)

theorem t78 : rows 101 400 ≤ 1035147627760756954 :=
  rows_le_of_split (by norm_num) (by norm_num) hr101 t79 (by norm_num)

theorem t77 : rows 100 400 ≤ 1035964952128221269 :=
  rows_le_of_split (by norm_num) (by norm_num) hr100 t78 (by norm_num)

theorem t76 : rows 99 400 ≤ 1036809183274879593 :=
  rows_le_of_split (by norm_num) (by norm_num) hr99 t77 (by norm_num)

theorem t75 : rows 98 400 ≤ 1037679898147279490 :=
  rows_le_of_split (by norm_num) (by norm_num) hr98 t76 (by norm_num)

theorem t74 : rows 97 400 ≤ 1038578025164340167 :=
  rows_le_of_split (by norm_num) (by norm_num) hr97 t75 (by norm_num)

theorem t73 : rows 96 400 ≤ 1039502990413233750 :=
  rows_le_of_split (by norm_num) (by norm_num) hr96 t74 (by norm_num)

theorem t72 : rows 95 400 ≤ 1040455810423129221 :=
  rows_le_of_split (by norm_num) (by norm_num) hr95 t73 (by norm_num)

theorem t71 : rows 94 400 ≤ 1041436992081720383 :=
  rows_le_of_split (by norm_num) (by norm_num) hr94 t72 (by norm_num)

theorem t70 : rows 93 400 ≤ 1042447934151029149 :=
  rows_le_of_split (by norm_num) (by norm_num) hr93 t71 (by norm_num)

theorem t69 : rows 92 400 ≤ 1043487913042308270 :=
  rows_le_of_split (by norm_num) (by norm_num) hr92 t70 (by norm_num)

theorem t68 : rows 91 400 ≤ 1044557606343889362 :=
  rows_le_of_split (by norm_num) (by norm_num) hr91 t69 (by norm_num)

theorem t67 : rows 90 400 ≤ 1045655806229563579 :=
  rows_le_of_split (by norm_num) (by norm_num) hr90 t68 (by norm_num)

theorem t66 : rows 89 400 ≤ 1046782734056629148 :=
  rows_le_of_split (by norm_num) (by norm_num) hr89 t67 (by norm_num)

theorem t65 : rows 88 400 ≤ 1047936914228091275 :=
  rows_le_of_split (by norm_num) (by norm_num) hr88 t66 (by norm_num)

theorem t64 : rows 87 400 ≤ 1049118212672967096 :=
  rows_le_of_split (by norm_num) (by norm_num) hr87 t65 (by norm_num)

theorem t63 : rows 86 400 ≤ 1050324817782683528 :=
  rows_le_of_split (by norm_num) (by norm_num) hr86 t64 (by norm_num)

theorem t62 : rows 85 400 ≤ 1051556413179891874 :=
  rows_le_of_split (by norm_num) (by norm_num) hr85 t63 (by norm_num)

theorem t61 : rows 84 400 ≤ 1052810920614602393 :=
  rows_le_of_split (by norm_num) (by norm_num) hr84 t62 (by norm_num)

theorem t60 : rows 83 400 ≤ 1054087753605591625 :=
  rows_le_of_split (by norm_num) (by norm_num) hr83 t61 (by norm_num)

theorem t59 : rows 82 400 ≤ 1055384713520258733 :=
  rows_le_of_split (by norm_num) (by norm_num) hr82 t60 (by norm_num)

theorem t58 : rows 81 400 ≤ 1056701009641990151 :=
  rows_le_of_split (by norm_num) (by norm_num) hr81 t59 (by norm_num)

theorem t57 : rows 80 400 ≤ 1058034282403183401 :=
  rows_le_of_split (by norm_num) (by norm_num) hr80 t58 (by norm_num)

theorem t56 : rows 79 400 ≤ 1059383728906590351 :=
  rows_le_of_split (by norm_num) (by norm_num) hr79 t57 (by norm_num)

theorem t55 : rows 78 400 ≤ 1060746885271958533 :=
  rows_le_of_split (by norm_num) (by norm_num) hr78 t56 (by norm_num)

theorem t54 : rows 77 400 ≤ 1062122832358794592 :=
  rows_le_of_split (by norm_num) (by norm_num) hr77 t55 (by norm_num)

theorem t53 : rows 76 400 ≤ 1063509152052735354 :=
  rows_le_of_split (by norm_num) (by norm_num) hr76 t54 (by norm_num)

theorem t52 : rows 75 400 ≤ 1064904987599690032 :=
  rows_le_of_split (by norm_num) (by norm_num) hr75 t53 (by norm_num)

theorem t51 : rows 74 400 ≤ 1066308055187753508 :=
  rows_le_of_split (by norm_num) (by norm_num) hr74 t52 (by norm_num)

theorem t50 : rows 73 400 ≤ 1067717736906082356 :=
  rows_le_of_split (by norm_num) (by norm_num) hr73 t51 (by norm_num)

theorem t49 : rows 72 400 ≤ 1069131880601476190 :=
  rows_le_of_split (by norm_num) (by norm_num) hr72 t50 (by norm_num)

theorem t48 : rows 71 400 ≤ 1070549973112772298 :=
  rows_le_of_split (by norm_num) (by norm_num) hr71 t49 (by norm_num)

theorem t47 : rows 70 400 ≤ 1071970075294455813 :=
  rows_le_of_split (by norm_num) (by norm_num) hr70 t48 (by norm_num)

theorem t46 : rows 69 400 ≤ 1073391779513980781 :=
  rows_le_of_split (by norm_num) (by norm_num) hr69 t47 (by norm_num)

theorem t45 : rows 68 400 ≤ 1074813231160315581 :=
  rows_le_of_split (by norm_num) (by norm_num) hr68 t46 (by norm_num)

theorem t44 : rows 67 400 ≤ 1076234210276962667 :=
  rows_le_of_split (by norm_num) (by norm_num) hr67 t45 (by norm_num)

theorem t43 : rows 66 400 ≤ 1077652949236013586 :=
  rows_le_of_split (by norm_num) (by norm_num) hr66 t44 (by norm_num)

theorem t42 : rows 65 400 ≤ 1079069293101341843 :=
  rows_le_of_split (by norm_num) (by norm_num) hr65 t43 (by norm_num)

theorem t41 : rows 64 400 ≤ 1080481642669968443 :=
  rows_le_of_split (by norm_num) (by norm_num) hr64 t42 (by norm_num)

theorem t40 : rows 63 400 ≤ 1081889912681555756 :=
  rows_le_of_split (by norm_num) (by norm_num) hr63 t41 (by norm_num)

theorem t39 : rows 62 400 ≤ 1083294209958340834 :=
  rows_le_of_split (by norm_num) (by norm_num) hr62 t40 (by norm_num)

theorem t38 : rows 61 400 ≤ 1084701097121409846 :=
  rows_le_of_split (by norm_num) (by norm_num) hr61 t39 (by norm_num)

theorem t37 : rows 60 400 ≤ 1086116727370187858 :=
  rows_le_of_split (by norm_num) (by norm_num) hr60 t38 (by norm_num)

theorem t36 : rows 59 400 ≤ 1087546343629533318 :=
  rows_le_of_split (by norm_num) (by norm_num) hr59 t37 (by norm_num)

theorem t35 : rows 58 400 ≤ 1088994472121198697 :=
  rows_le_of_split (by norm_num) (by norm_num) hr58 t36 (by norm_num)

theorem t34 : rows 57 400 ≤ 1090464738876407999 :=
  rows_le_of_split (by norm_num) (by norm_num) hr57 t35 (by norm_num)

theorem t33 : rows 56 400 ≤ 1091960124302378115 :=
  rows_le_of_split (by norm_num) (by norm_num) hr56 t34 (by norm_num)

theorem t32 : rows 55 400 ≤ 1093482884399421117 :=
  rows_le_of_split (by norm_num) (by norm_num) hr55 t33 (by norm_num)

theorem t31 : rows 54 400 ≤ 1095034511565163454 :=
  rows_le_of_split (by norm_num) (by norm_num) hr54 t32 (by norm_num)

theorem t30 : rows 53 400 ≤ 1096615552706892444 :=
  rows_le_of_split (by norm_num) (by norm_num) hr53 t31 (by norm_num)

theorem t29 : rows 52 400 ≤ 1098225790891066532 :=
  rows_le_of_split (by norm_num) (by norm_num) hr52 t30 (by norm_num)

theorem t28 : rows 51 400 ≤ 1099864012810697133 :=
  rows_le_of_split (by norm_num) (by norm_num) hr51 t29 (by norm_num)

theorem t27 : rows 50 400 ≤ 1101528229696385341 :=
  rows_le_of_split (by norm_num) (by norm_num) hr50 t28 (by norm_num)

theorem t26 : rows 49 400 ≤ 1103215595571740790 :=
  rows_le_of_split (by norm_num) (by norm_num) hr49 t27 (by norm_num)

theorem t25 : rows 48 400 ≤ 1104922416336609764 :=
  rows_le_of_split (by norm_num) (by norm_num) hr48 t26 (by norm_num)

theorem t24 : rows 47 400 ≤ 1106644108042851653 :=
  rows_le_of_split (by norm_num) (by norm_num) hr47 t25 (by norm_num)

theorem t23 : rows 46 400 ≤ 1108375355001763561 :=
  rows_le_of_split (by norm_num) (by norm_num) hr46 t24 (by norm_num)

theorem t22 : rows 45 400 ≤ 1110109861026347727 :=
  rows_le_of_split (by norm_num) (by norm_num) hr45 t23 (by norm_num)

theorem t21 : rows 44 400 ≤ 1111840800422475166 :=
  rows_le_of_split (by norm_num) (by norm_num) hr44 t22 (by norm_num)

theorem t20 : rows 43 400 ≤ 1113560829135048425 :=
  rows_le_of_split (by norm_num) (by norm_num) hr43 t21 (by norm_num)

theorem t19 : rows 42 400 ≤ 1115262119466224497 :=
  rows_le_of_split (by norm_num) (by norm_num) hr42 t20 (by norm_num)

theorem t18 : rows 41 400 ≤ 1116936304651785786 :=
  rows_le_of_split (by norm_num) (by norm_num) hr41 t19 (by norm_num)

theorem t17 : rows 40 400 ≤ 1118574961097312332 :=
  rows_le_of_split (by norm_num) (by norm_num) hr40 t18 (by norm_num)

theorem t16 : rows 39 400 ≤ 1120170603190086305 :=
  rows_le_of_split (by norm_num) (by norm_num) hr39 t17 (by norm_num)

theorem t15 : rows 38 400 ≤ 1121716826667860287 :=
  rows_le_of_split (by norm_num) (by norm_num) hr38 t16 (by norm_num)

theorem t14 : rows 37 400 ≤ 1123208258490633281 :=
  rows_le_of_split (by norm_num) (by norm_num) hr37 t15 (by norm_num)

theorem t13 : rows 36 400 ≤ 1124640438506051404 :=
  rows_le_of_split (by norm_num) (by norm_num) hr36 t14 (by norm_num)

theorem t12 : rows 35 400 ≤ 1126009865275755430 :=
  rows_le_of_split (by norm_num) (by norm_num) hr35 t13 (by norm_num)

theorem t11 : rows 34 400 ≤ 1127313971420731529 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_11 t12 (by norm_num)

theorem t10 : rows 33 400 ≤ 1128551028889365533 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_10 t11 (by norm_num)

theorem t9 : rows 32 400 ≤ 1129720214198129425 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_9 t10 (by norm_num)

theorem t8 : rows 31 400 ≤ 1130821602454064305 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_8 t9 (by norm_num)

theorem t7 : rows 30 400 ≤ 1131856090729285106 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_7 t8 (by norm_num)

theorem t6 : rows 29 400 ≤ 1132825174970687099 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_6 t7 (by norm_num)

theorem t5 : rows 28 400 ≤ 1133730421929255516 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_5 t6 (by norm_num)

theorem t4 : rows 27 400 ≤ 1134573470287497925 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_4 t5 (by norm_num)

theorem t3 : rows 25 400 ≤ 1136079891099546335 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_3 t4 (by norm_num)

theorem t2 : rows 23 400 ≤ 1137359016169114095 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_2 t3 (by norm_num)

theorem t1 : rows 19 400 ≤ 1139299614553431326 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_1 t2 (by norm_num)

theorem t0 : rows 0 400 ≤ 1141621279451627817 :=
  rows_le_of_split (by norm_num) (by norm_num) rows225C_0 t1 (by norm_num)

/-- **The certificate on `grid225C`**: the loss's bound is less than `K`, the 1374 parts checked by the kernel. -/
theorem total_lt_225C : total < K := by
  rw [total_eq_rows_full]
  exact lt_of_le_of_lt t0 (by decide +kernel)

end

end SieveCert

#print axioms SieveCert.total_lt_225C
