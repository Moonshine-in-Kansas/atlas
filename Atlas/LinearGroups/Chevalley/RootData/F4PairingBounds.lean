import Atlas.LinearGroups.Chevalley.RootData.F4

/-! Exact small root-table bounds; ordinary kernel computation. -/
namespace Atlas.Chevalley.F4Table
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem pairing_bounds_row_0 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 0) ∧
      dot (dualCoordinates b) (coordinates 0) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_1 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 1) ∧
      dot (dualCoordinates b) (coordinates 1) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_2 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 2) ∧
      dot (dualCoordinates b) (coordinates 2) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_3 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 3) ∧
      dot (dualCoordinates b) (coordinates 3) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_4 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 4) ∧
      dot (dualCoordinates b) (coordinates 4) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_5 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 5) ∧
      dot (dualCoordinates b) (coordinates 5) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_6 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 6) ∧
      dot (dualCoordinates b) (coordinates 6) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_7 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 7) ∧
      dot (dualCoordinates b) (coordinates 7) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_8 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 8) ∧
      dot (dualCoordinates b) (coordinates 8) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_9 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 9) ∧
      dot (dualCoordinates b) (coordinates 9) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_10 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 10) ∧
      dot (dualCoordinates b) (coordinates 10) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_11 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 11) ∧
      dot (dualCoordinates b) (coordinates 11) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_12 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 12) ∧
      dot (dualCoordinates b) (coordinates 12) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_13 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 13) ∧
      dot (dualCoordinates b) (coordinates 13) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_14 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 14) ∧
      dot (dualCoordinates b) (coordinates 14) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_15 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 15) ∧
      dot (dualCoordinates b) (coordinates 15) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_16 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 16) ∧
      dot (dualCoordinates b) (coordinates 16) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_17 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 17) ∧
      dot (dualCoordinates b) (coordinates 17) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_18 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 18) ∧
      dot (dualCoordinates b) (coordinates 18) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_19 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 19) ∧
      dot (dualCoordinates b) (coordinates 19) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_20 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 20) ∧
      dot (dualCoordinates b) (coordinates 20) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_21 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 21) ∧
      dot (dualCoordinates b) (coordinates 21) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_22 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 22) ∧
      dot (dualCoordinates b) (coordinates 22) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_23 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 23) ∧
      dot (dualCoordinates b) (coordinates 23) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_24 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 24) ∧
      dot (dualCoordinates b) (coordinates 24) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_25 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 25) ∧
      dot (dualCoordinates b) (coordinates 25) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_26 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 26) ∧
      dot (dualCoordinates b) (coordinates 26) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_27 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 27) ∧
      dot (dualCoordinates b) (coordinates 27) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_28 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 28) ∧
      dot (dualCoordinates b) (coordinates 28) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_29 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 29) ∧
      dot (dualCoordinates b) (coordinates 29) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_30 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 30) ∧
      dot (dualCoordinates b) (coordinates 30) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_31 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 31) ∧
      dot (dualCoordinates b) (coordinates 31) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_32 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 32) ∧
      dot (dualCoordinates b) (coordinates 32) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_33 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 33) ∧
      dot (dualCoordinates b) (coordinates 33) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_34 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 34) ∧
      dot (dualCoordinates b) (coordinates 34) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_35 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 35) ∧
      dot (dualCoordinates b) (coordinates 35) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_36 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 36) ∧
      dot (dualCoordinates b) (coordinates 36) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_37 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 37) ∧
      dot (dualCoordinates b) (coordinates 37) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_38 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 38) ∧
      dot (dualCoordinates b) (coordinates 38) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_39 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 39) ∧
      dot (dualCoordinates b) (coordinates 39) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_40 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 40) ∧
      dot (dualCoordinates b) (coordinates 40) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_41 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 41) ∧
      dot (dualCoordinates b) (coordinates 41) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_42 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 42) ∧
      dot (dualCoordinates b) (coordinates 42) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_43 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 43) ∧
      dot (dualCoordinates b) (coordinates 43) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_44 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 44) ∧
      dot (dualCoordinates b) (coordinates 44) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_45 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 45) ∧
      dot (dualCoordinates b) (coordinates 45) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_46 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 46) ∧
      dot (dualCoordinates b) (coordinates 46) ≤ 2 := by decide +kernel
private theorem pairing_bounds_row_47 : ∀ b : Root,
    -2 ≤ dot (dualCoordinates b) (coordinates 47) ∧
      dot (dualCoordinates b) (coordinates 47) ≤ 2 := by decide +kernel

theorem all_pairing_bounds (a b : Root) :
    -2 ≤ dot (dualCoordinates b) (coordinates a) ∧
      dot (dualCoordinates b) (coordinates a) ≤ 2 := by
  fin_cases a
  · exact pairing_bounds_row_0 b
  · exact pairing_bounds_row_1 b
  · exact pairing_bounds_row_2 b
  · exact pairing_bounds_row_3 b
  · exact pairing_bounds_row_4 b
  · exact pairing_bounds_row_5 b
  · exact pairing_bounds_row_6 b
  · exact pairing_bounds_row_7 b
  · exact pairing_bounds_row_8 b
  · exact pairing_bounds_row_9 b
  · exact pairing_bounds_row_10 b
  · exact pairing_bounds_row_11 b
  · exact pairing_bounds_row_12 b
  · exact pairing_bounds_row_13 b
  · exact pairing_bounds_row_14 b
  · exact pairing_bounds_row_15 b
  · exact pairing_bounds_row_16 b
  · exact pairing_bounds_row_17 b
  · exact pairing_bounds_row_18 b
  · exact pairing_bounds_row_19 b
  · exact pairing_bounds_row_20 b
  · exact pairing_bounds_row_21 b
  · exact pairing_bounds_row_22 b
  · exact pairing_bounds_row_23 b
  · exact pairing_bounds_row_24 b
  · exact pairing_bounds_row_25 b
  · exact pairing_bounds_row_26 b
  · exact pairing_bounds_row_27 b
  · exact pairing_bounds_row_28 b
  · exact pairing_bounds_row_29 b
  · exact pairing_bounds_row_30 b
  · exact pairing_bounds_row_31 b
  · exact pairing_bounds_row_32 b
  · exact pairing_bounds_row_33 b
  · exact pairing_bounds_row_34 b
  · exact pairing_bounds_row_35 b
  · exact pairing_bounds_row_36 b
  · exact pairing_bounds_row_37 b
  · exact pairing_bounds_row_38 b
  · exact pairing_bounds_row_39 b
  · exact pairing_bounds_row_40 b
  · exact pairing_bounds_row_41 b
  · exact pairing_bounds_row_42 b
  · exact pairing_bounds_row_43 b
  · exact pairing_bounds_row_44 b
  · exact pairing_bounds_row_45 b
  · exact pairing_bounds_row_46 b
  · exact pairing_bounds_row_47 b

end Atlas.Chevalley.F4Table

namespace Atlas.Chevalley.F4Data

theorem pairing_bounds (a b : Root) :
    -2 ≤ pairing.pairing a b ∧ pairing.pairing a b ≤ 2 := by
  change -2 ≤ F4Table.dot (F4Table.dualCoordinates b) (F4Table.coordinates a) ∧
    F4Table.dot (F4Table.dualCoordinates b) (F4Table.coordinates a) ≤ 2
  exact F4Table.all_pairing_bounds a b

end Atlas.Chevalley.F4Data
