import Atlas.LinearGroups.Chevalley.RootData.F4Table.Data

/-! F4 root certificate component: Primitive. -/
namespace Atlas.Chevalley.F4Table
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem primitive_0 : dot (primitiveWitnessCoordinates 0) (coordinates 0) = 1 := by decide +kernel
private theorem primitive_1 : dot (primitiveWitnessCoordinates 1) (coordinates 1) = 1 := by decide +kernel
private theorem primitive_2 : dot (primitiveWitnessCoordinates 2) (coordinates 2) = 1 := by decide +kernel
private theorem primitive_3 : dot (primitiveWitnessCoordinates 3) (coordinates 3) = 1 := by decide +kernel
private theorem primitive_4 : dot (primitiveWitnessCoordinates 4) (coordinates 4) = 1 := by decide +kernel
private theorem primitive_5 : dot (primitiveWitnessCoordinates 5) (coordinates 5) = 1 := by decide +kernel
private theorem primitive_6 : dot (primitiveWitnessCoordinates 6) (coordinates 6) = 1 := by decide +kernel
private theorem primitive_7 : dot (primitiveWitnessCoordinates 7) (coordinates 7) = 1 := by decide +kernel
private theorem primitive_8 : dot (primitiveWitnessCoordinates 8) (coordinates 8) = 1 := by decide +kernel
private theorem primitive_9 : dot (primitiveWitnessCoordinates 9) (coordinates 9) = 1 := by decide +kernel
private theorem primitive_10 : dot (primitiveWitnessCoordinates 10) (coordinates 10) = 1 := by decide +kernel
private theorem primitive_11 : dot (primitiveWitnessCoordinates 11) (coordinates 11) = 1 := by decide +kernel
private theorem primitive_12 : dot (primitiveWitnessCoordinates 12) (coordinates 12) = 1 := by decide +kernel
private theorem primitive_13 : dot (primitiveWitnessCoordinates 13) (coordinates 13) = 1 := by decide +kernel
private theorem primitive_14 : dot (primitiveWitnessCoordinates 14) (coordinates 14) = 1 := by decide +kernel
private theorem primitive_15 : dot (primitiveWitnessCoordinates 15) (coordinates 15) = 1 := by decide +kernel
private theorem primitive_16 : dot (primitiveWitnessCoordinates 16) (coordinates 16) = 1 := by decide +kernel
private theorem primitive_17 : dot (primitiveWitnessCoordinates 17) (coordinates 17) = 1 := by decide +kernel
private theorem primitive_18 : dot (primitiveWitnessCoordinates 18) (coordinates 18) = 1 := by decide +kernel
private theorem primitive_19 : dot (primitiveWitnessCoordinates 19) (coordinates 19) = 1 := by decide +kernel
private theorem primitive_20 : dot (primitiveWitnessCoordinates 20) (coordinates 20) = 1 := by decide +kernel
private theorem primitive_21 : dot (primitiveWitnessCoordinates 21) (coordinates 21) = 1 := by decide +kernel
private theorem primitive_22 : dot (primitiveWitnessCoordinates 22) (coordinates 22) = 1 := by decide +kernel
private theorem primitive_23 : dot (primitiveWitnessCoordinates 23) (coordinates 23) = 1 := by decide +kernel
private theorem primitive_24 : dot (primitiveWitnessCoordinates 24) (coordinates 24) = 1 := by decide +kernel
private theorem primitive_25 : dot (primitiveWitnessCoordinates 25) (coordinates 25) = 1 := by decide +kernel
private theorem primitive_26 : dot (primitiveWitnessCoordinates 26) (coordinates 26) = 1 := by decide +kernel
private theorem primitive_27 : dot (primitiveWitnessCoordinates 27) (coordinates 27) = 1 := by decide +kernel
private theorem primitive_28 : dot (primitiveWitnessCoordinates 28) (coordinates 28) = 1 := by decide +kernel
private theorem primitive_29 : dot (primitiveWitnessCoordinates 29) (coordinates 29) = 1 := by decide +kernel
private theorem primitive_30 : dot (primitiveWitnessCoordinates 30) (coordinates 30) = 1 := by decide +kernel
private theorem primitive_31 : dot (primitiveWitnessCoordinates 31) (coordinates 31) = 1 := by decide +kernel
private theorem primitive_32 : dot (primitiveWitnessCoordinates 32) (coordinates 32) = 1 := by decide +kernel
private theorem primitive_33 : dot (primitiveWitnessCoordinates 33) (coordinates 33) = 1 := by decide +kernel
private theorem primitive_34 : dot (primitiveWitnessCoordinates 34) (coordinates 34) = 1 := by decide +kernel
private theorem primitive_35 : dot (primitiveWitnessCoordinates 35) (coordinates 35) = 1 := by decide +kernel
private theorem primitive_36 : dot (primitiveWitnessCoordinates 36) (coordinates 36) = 1 := by decide +kernel
private theorem primitive_37 : dot (primitiveWitnessCoordinates 37) (coordinates 37) = 1 := by decide +kernel
private theorem primitive_38 : dot (primitiveWitnessCoordinates 38) (coordinates 38) = 1 := by decide +kernel
private theorem primitive_39 : dot (primitiveWitnessCoordinates 39) (coordinates 39) = 1 := by decide +kernel
private theorem primitive_40 : dot (primitiveWitnessCoordinates 40) (coordinates 40) = 1 := by decide +kernel
private theorem primitive_41 : dot (primitiveWitnessCoordinates 41) (coordinates 41) = 1 := by decide +kernel
private theorem primitive_42 : dot (primitiveWitnessCoordinates 42) (coordinates 42) = 1 := by decide +kernel
private theorem primitive_43 : dot (primitiveWitnessCoordinates 43) (coordinates 43) = 1 := by decide +kernel
private theorem primitive_44 : dot (primitiveWitnessCoordinates 44) (coordinates 44) = 1 := by decide +kernel
private theorem primitive_45 : dot (primitiveWitnessCoordinates 45) (coordinates 45) = 1 := by decide +kernel
private theorem primitive_46 : dot (primitiveWitnessCoordinates 46) (coordinates 46) = 1 := by decide +kernel
private theorem primitive_47 : dot (primitiveWitnessCoordinates 47) (coordinates 47) = 1 := by decide +kernel
theorem primitive : ∀ a : Root, dot (primitiveWitnessCoordinates a) (coordinates a) = 1 := by
  intro a
  fin_cases a
  · exact primitive_0
  · exact primitive_1
  · exact primitive_2
  · exact primitive_3
  · exact primitive_4
  · exact primitive_5
  · exact primitive_6
  · exact primitive_7
  · exact primitive_8
  · exact primitive_9
  · exact primitive_10
  · exact primitive_11
  · exact primitive_12
  · exact primitive_13
  · exact primitive_14
  · exact primitive_15
  · exact primitive_16
  · exact primitive_17
  · exact primitive_18
  · exact primitive_19
  · exact primitive_20
  · exact primitive_21
  · exact primitive_22
  · exact primitive_23
  · exact primitive_24
  · exact primitive_25
  · exact primitive_26
  · exact primitive_27
  · exact primitive_28
  · exact primitive_29
  · exact primitive_30
  · exact primitive_31
  · exact primitive_32
  · exact primitive_33
  · exact primitive_34
  · exact primitive_35
  · exact primitive_36
  · exact primitive_37
  · exact primitive_38
  · exact primitive_39
  · exact primitive_40
  · exact primitive_41
  · exact primitive_42
  · exact primitive_43
  · exact primitive_44
  · exact primitive_45
  · exact primitive_46
  · exact primitive_47

end Atlas.Chevalley.F4Table
