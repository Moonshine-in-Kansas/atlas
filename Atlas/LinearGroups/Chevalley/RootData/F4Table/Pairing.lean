import Atlas.LinearGroups.Chevalley.RootData.F4Table.Data

/-! F4 root certificate component: Pairing. -/
namespace Atlas.Chevalley.F4Table
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem pairing_two_0 : dot (dualCoordinates 0) (coordinates 0) = 2 := by decide +kernel
private theorem pairing_two_1 : dot (dualCoordinates 1) (coordinates 1) = 2 := by decide +kernel
private theorem pairing_two_2 : dot (dualCoordinates 2) (coordinates 2) = 2 := by decide +kernel
private theorem pairing_two_3 : dot (dualCoordinates 3) (coordinates 3) = 2 := by decide +kernel
private theorem pairing_two_4 : dot (dualCoordinates 4) (coordinates 4) = 2 := by decide +kernel
private theorem pairing_two_5 : dot (dualCoordinates 5) (coordinates 5) = 2 := by decide +kernel
private theorem pairing_two_6 : dot (dualCoordinates 6) (coordinates 6) = 2 := by decide +kernel
private theorem pairing_two_7 : dot (dualCoordinates 7) (coordinates 7) = 2 := by decide +kernel
private theorem pairing_two_8 : dot (dualCoordinates 8) (coordinates 8) = 2 := by decide +kernel
private theorem pairing_two_9 : dot (dualCoordinates 9) (coordinates 9) = 2 := by decide +kernel
private theorem pairing_two_10 : dot (dualCoordinates 10) (coordinates 10) = 2 := by decide +kernel
private theorem pairing_two_11 : dot (dualCoordinates 11) (coordinates 11) = 2 := by decide +kernel
private theorem pairing_two_12 : dot (dualCoordinates 12) (coordinates 12) = 2 := by decide +kernel
private theorem pairing_two_13 : dot (dualCoordinates 13) (coordinates 13) = 2 := by decide +kernel
private theorem pairing_two_14 : dot (dualCoordinates 14) (coordinates 14) = 2 := by decide +kernel
private theorem pairing_two_15 : dot (dualCoordinates 15) (coordinates 15) = 2 := by decide +kernel
private theorem pairing_two_16 : dot (dualCoordinates 16) (coordinates 16) = 2 := by decide +kernel
private theorem pairing_two_17 : dot (dualCoordinates 17) (coordinates 17) = 2 := by decide +kernel
private theorem pairing_two_18 : dot (dualCoordinates 18) (coordinates 18) = 2 := by decide +kernel
private theorem pairing_two_19 : dot (dualCoordinates 19) (coordinates 19) = 2 := by decide +kernel
private theorem pairing_two_20 : dot (dualCoordinates 20) (coordinates 20) = 2 := by decide +kernel
private theorem pairing_two_21 : dot (dualCoordinates 21) (coordinates 21) = 2 := by decide +kernel
private theorem pairing_two_22 : dot (dualCoordinates 22) (coordinates 22) = 2 := by decide +kernel
private theorem pairing_two_23 : dot (dualCoordinates 23) (coordinates 23) = 2 := by decide +kernel
private theorem pairing_two_24 : dot (dualCoordinates 24) (coordinates 24) = 2 := by decide +kernel
private theorem pairing_two_25 : dot (dualCoordinates 25) (coordinates 25) = 2 := by decide +kernel
private theorem pairing_two_26 : dot (dualCoordinates 26) (coordinates 26) = 2 := by decide +kernel
private theorem pairing_two_27 : dot (dualCoordinates 27) (coordinates 27) = 2 := by decide +kernel
private theorem pairing_two_28 : dot (dualCoordinates 28) (coordinates 28) = 2 := by decide +kernel
private theorem pairing_two_29 : dot (dualCoordinates 29) (coordinates 29) = 2 := by decide +kernel
private theorem pairing_two_30 : dot (dualCoordinates 30) (coordinates 30) = 2 := by decide +kernel
private theorem pairing_two_31 : dot (dualCoordinates 31) (coordinates 31) = 2 := by decide +kernel
private theorem pairing_two_32 : dot (dualCoordinates 32) (coordinates 32) = 2 := by decide +kernel
private theorem pairing_two_33 : dot (dualCoordinates 33) (coordinates 33) = 2 := by decide +kernel
private theorem pairing_two_34 : dot (dualCoordinates 34) (coordinates 34) = 2 := by decide +kernel
private theorem pairing_two_35 : dot (dualCoordinates 35) (coordinates 35) = 2 := by decide +kernel
private theorem pairing_two_36 : dot (dualCoordinates 36) (coordinates 36) = 2 := by decide +kernel
private theorem pairing_two_37 : dot (dualCoordinates 37) (coordinates 37) = 2 := by decide +kernel
private theorem pairing_two_38 : dot (dualCoordinates 38) (coordinates 38) = 2 := by decide +kernel
private theorem pairing_two_39 : dot (dualCoordinates 39) (coordinates 39) = 2 := by decide +kernel
private theorem pairing_two_40 : dot (dualCoordinates 40) (coordinates 40) = 2 := by decide +kernel
private theorem pairing_two_41 : dot (dualCoordinates 41) (coordinates 41) = 2 := by decide +kernel
private theorem pairing_two_42 : dot (dualCoordinates 42) (coordinates 42) = 2 := by decide +kernel
private theorem pairing_two_43 : dot (dualCoordinates 43) (coordinates 43) = 2 := by decide +kernel
private theorem pairing_two_44 : dot (dualCoordinates 44) (coordinates 44) = 2 := by decide +kernel
private theorem pairing_two_45 : dot (dualCoordinates 45) (coordinates 45) = 2 := by decide +kernel
private theorem pairing_two_46 : dot (dualCoordinates 46) (coordinates 46) = 2 := by decide +kernel
private theorem pairing_two_47 : dot (dualCoordinates 47) (coordinates 47) = 2 := by decide +kernel
theorem pairing_two : ∀ a : Root, dot (dualCoordinates a) (coordinates a) = 2 := by
  intro a
  fin_cases a
  · exact pairing_two_0
  · exact pairing_two_1
  · exact pairing_two_2
  · exact pairing_two_3
  · exact pairing_two_4
  · exact pairing_two_5
  · exact pairing_two_6
  · exact pairing_two_7
  · exact pairing_two_8
  · exact pairing_two_9
  · exact pairing_two_10
  · exact pairing_two_11
  · exact pairing_two_12
  · exact pairing_two_13
  · exact pairing_two_14
  · exact pairing_two_15
  · exact pairing_two_16
  · exact pairing_two_17
  · exact pairing_two_18
  · exact pairing_two_19
  · exact pairing_two_20
  · exact pairing_two_21
  · exact pairing_two_22
  · exact pairing_two_23
  · exact pairing_two_24
  · exact pairing_two_25
  · exact pairing_two_26
  · exact pairing_two_27
  · exact pairing_two_28
  · exact pairing_two_29
  · exact pairing_two_30
  · exact pairing_two_31
  · exact pairing_two_32
  · exact pairing_two_33
  · exact pairing_two_34
  · exact pairing_two_35
  · exact pairing_two_36
  · exact pairing_two_37
  · exact pairing_two_38
  · exact pairing_two_39
  · exact pairing_two_40
  · exact pairing_two_41
  · exact pairing_two_42
  · exact pairing_two_43
  · exact pairing_two_44
  · exact pairing_two_45
  · exact pairing_two_46
  · exact pairing_two_47

end Atlas.Chevalley.F4Table
