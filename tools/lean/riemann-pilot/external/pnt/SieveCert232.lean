/-
# Round 609: the certificate of the sieve route's loss at `L = 232/100` (the unconditional exponent)

The grid of `SieveTypeIIU232.typeII_232`'s window: `U1 = ⌈(4045/10000)DEN⌉`, `U2 = ⌊(4825/10000)DEN⌋`, `n = 150`. On
it `SieveCert.total` is at most `0.88K`, checked by the kernel in 25 parts: `rows a b` is the sum of the rows
`a ≤ i < b` of the total (defined here until round 618 moved it to `SieveCertDefs.lean` and `rows_eq` to
`SieveCert.lean`), the total is the sum of its 25 parts (`total_eq_rows`; from 2 to 30 rows each, grouped by the
kernel's work), and each part is bounded by `decide +kernel` (`rows_0` … `rows_24`), one at a time (`Elab.async
false`). One kernel check of the whole grid at `n = 150` needs more memory than the shell's memory cgroup allows (it was
killed below the shell's cgroup limit, 13.36 GiB in the present container; the machine has 16), and the kernel frees a
part's memory before the next; a part of 15 rows took up to 7.4 GB (scratch).

The file imports `SieveCert.lean`.
-/
import SieveCert

/-! The 25 kernel checks run one at a time: with asynchronous elaboration they would run together and need
the memory of the whole grid. -/
set_option Elab.async false

namespace SieveCert

/-- **The grid at `L = 232/100`**: `U1 = ⌈(4045/10000)DEN⌉`, `U2 = ⌊(4825/10000)DEN⌋`, `n = 150`. -/
@[instance_reducible] def grid232 : Grid := ⟨(4045 * DEN + 9999) / 10000, 4825 * DEN / 10000, 150⟩

theorem gridOK232 : @GridOK grid232 :=
  @GridOK.mk grid232 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The total of a grid with `n = 150` is the sum of its 25 parts. -/
theorem total_eq_rows_of [Grid] (hn : n = 150) : total =
    rows 0 17 + (rows 17 23 + (rows 23 27 + (rows 27 31 + (rows 31 35 + (rows 35 39 + (rows 39 43 + (rows 43 47 +
      (rows 47 52 + (rows 52 57 + (rows 57 62 + (rows 62 66 + (rows 66 71 + (rows 71 77 + (rows 77 84 +
      (rows 84 90 + (rows 90 95 + (rows 95 99 + (rows 99 103 + (rows 103 107 + (rows 107 111 + (rows 111 115 +
      (rows 115 145 + (rows 145 148 + (rows 148 150)))))))))))))))))))))))) := by
  simp only [total_eq, rows_eq, hn, Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 0 ≤ 17) (by norm_num : 17 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 17 ≤ 23) (by norm_num : 23 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 23 ≤ 27) (by norm_num : 27 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 27 ≤ 31) (by norm_num : 31 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 31 ≤ 35) (by norm_num : 35 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 35 ≤ 39) (by norm_num : 39 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 39 ≤ 43) (by norm_num : 43 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 43 ≤ 47) (by norm_num : 47 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 47 ≤ 52) (by norm_num : 52 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 52 ≤ 57) (by norm_num : 57 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 57 ≤ 62) (by norm_num : 62 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 62 ≤ 66) (by norm_num : 66 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 66 ≤ 71) (by norm_num : 71 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 71 ≤ 77) (by norm_num : 77 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 77 ≤ 84) (by norm_num : 84 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 84 ≤ 90) (by norm_num : 90 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 90 ≤ 95) (by norm_num : 95 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 95 ≤ 99) (by norm_num : 99 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 99 ≤ 103) (by norm_num : 103 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 103 ≤ 107) (by norm_num : 107 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 107 ≤ 111) (by norm_num : 111 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 111 ≤ 115) (by norm_num : 115 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 115 ≤ 145) (by norm_num : 145 ≤ 150),
      ← Finset.sum_Ico_consecutive _ (by norm_num : 145 ≤ 148) (by norm_num : 148 ≤ 150)]

section

attribute [local instance] grid232

/-- **The total on `grid232` is the sum of its 25 parts.** -/
theorem total_eq_rows : total =
    rows 0 17 + (rows 17 23 + (rows 23 27 + (rows 27 31 + (rows 31 35 + (rows 35 39 + (rows 39 43 + (rows 43 47 +
      (rows 47 52 + (rows 52 57 + (rows 57 62 + (rows 62 66 + (rows 66 71 + (rows 71 77 + (rows 77 84 +
      (rows 84 90 + (rows 90 95 + (rows 95 99 + (rows 99 103 + (rows 103 107 + (rows 107 111 + (rows 111 115 +
      (rows 115 145 + (rows 145 148 + (rows 148 150)))))))))))))))))))))))) := total_eq_rows_of rfl

theorem rows_0 : rows 0 17 ≤ 16529915989778914 := by decide +kernel

theorem rows_1 : rows 17 23 ≤ 8852099713741203 := by decide +kernel

theorem rows_2 : rows 23 27 ≤ 8475095088378400 := by decide +kernel

theorem rows_3 : rows 27 31 ≤ 8019961848844023 := by decide +kernel

theorem rows_4 : rows 31 35 ≤ 6292928200926776 := by decide +kernel

theorem rows_5 : rows 35 39 ≤ 4717754046497998 := by decide +kernel

theorem rows_6 : rows 39 43 ≤ 4090478254356229 := by decide +kernel

theorem rows_7 : rows 43 47 ≤ 10299953226337858 := by decide +kernel

theorem rows_8 : rows 47 52 ≤ 5724719784267682 := by decide +kernel

theorem rows_9 : rows 52 57 ≤ 1281081309408723 := by decide +kernel

theorem rows_10 : rows 57 62 ≤ 8632976408640355 := by decide +kernel

theorem rows_11 : rows 62 66 ≤ 18637907056608912 := by decide +kernel

theorem rows_12 : rows 66 71 ≤ 27477447713597544 := by decide +kernel

theorem rows_13 : rows 71 77 ≤ 35821380770799428 := by decide +kernel

theorem rows_14 : rows 77 84 ≤ 56102831918439208 := by decide +kernel

theorem rows_15 : rows 84 90 ≤ 73489220677066016 := by decide +kernel

theorem rows_16 : rows 90 95 ≤ 77773944129978528 := by decide +kernel

theorem rows_17 : rows 95 99 ≤ 69541646065088976 := by decide +kernel

theorem rows_18 : rows 99 103 ≤ 77189925580593280 := by decide +kernel

theorem rows_19 : rows 103 107 ≤ 83938665333880416 := by decide +kernel

theorem rows_20 : rows 107 111 ≤ 83903401593423904 := by decide +kernel

theorem rows_21 : rows 111 115 ≤ 83627231816918240 := by decide +kernel

theorem rows_22 : rows 115 145 ≤ 86138699494802464 := by decide +kernel

theorem rows_23 : rows 145 148 ≤ 72539350341664928 := by decide +kernel

theorem rows_24 : rows 148 150 ≤ 52763398136597224 := by decide +kernel

/-- **The certificate on `grid232`**: the loss's bound is at most `0.88`, the 25 parts checked by the kernel. -/
theorem total_le_232 : total ≤ 88 * K / 100 := by
  rw [total_eq_rows]
  have h0 := rows_0
  have h1 := rows_1
  have h2 := rows_2
  have h3 := rows_3
  have h4 := rows_4
  have h5 := rows_5
  have h6 := rows_6
  have h7 := rows_7
  have h8 := rows_8
  have h9 := rows_9
  have h10 := rows_10
  have h11 := rows_11
  have h12 := rows_12
  have h13 := rows_13
  have h14 := rows_14
  have h15 := rows_15
  have h16 := rows_16
  have h17 := rows_17
  have h18 := rows_18
  have h19 := rows_19
  have h20 := rows_20
  have h21 := rows_21
  have h22 := rows_22
  have h23 := rows_23
  have h24 := rows_24
  have hs :
      rows 0 17 + (rows 17 23 + (rows 23 27 + (rows 27 31 + (rows 31 35 + (rows 35 39 + (rows 39 43 + (rows 43 47 +
        (rows 47 52 + (rows 52 57 + (rows 57 62 + (rows 62 66 + (rows 66 71 + (rows 71 77 + (rows 77 84 +
        (rows 84 90 + (rows 90 95 + (rows 95 99 + (rows 99 103 + (rows 103 107 + (rows 107 111 + (rows 111 115 +
        (rows 115 145 + (rows 145 148 + (rows 148 150)))))))))))))))))))))))) ≤
      16529915989778914 + (8852099713741203 + (8475095088378400 + (8019961848844023 + (6292928200926776 +
        (4717754046497998 + (4090478254356229 + (10299953226337858 + (5724719784267682 + (1281081309408723 +
        (8632976408640355 + (18637907056608912 + (27477447713597544 + (35821380770799428 + (56102831918439208 +
        (73489220677066016 + (77773944129978528 + (69541646065088976 + (77189925580593280 + (83938665333880416 +
        (83903401593423904 + (83627231816918240 + (86138699494802464 + (72539350341664928 +
        (52763398136597224)))))))))))))))))))))))) := by
    omega
  exact hs.trans (by decide +kernel)

end

end SieveCert

#print axioms SieveCert.gridOK232
#print axioms SieveCert.total_eq_rows
#print axioms SieveCert.total_le_232
