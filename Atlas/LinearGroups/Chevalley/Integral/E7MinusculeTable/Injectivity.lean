import Atlas.LinearGroups.Chevalley.Integral.E7MinusculeTable.Data

/-! E7 minuscule certificate component: Injectivity. -/
namespace Atlas.Chevalley.E7MinusculeTable
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem decode_coordinates_0 : decode (coordinates 0) = 0 := by decide +kernel
private theorem decode_coordinates_1 : decode (coordinates 1) = 1 := by decide +kernel
private theorem decode_coordinates_2 : decode (coordinates 2) = 2 := by decide +kernel
private theorem decode_coordinates_3 : decode (coordinates 3) = 3 := by decide +kernel
private theorem decode_coordinates_4 : decode (coordinates 4) = 4 := by decide +kernel
private theorem decode_coordinates_5 : decode (coordinates 5) = 5 := by decide +kernel
private theorem decode_coordinates_6 : decode (coordinates 6) = 6 := by decide +kernel
private theorem decode_coordinates_7 : decode (coordinates 7) = 7 := by decide +kernel
private theorem decode_coordinates_8 : decode (coordinates 8) = 8 := by decide +kernel
private theorem decode_coordinates_9 : decode (coordinates 9) = 9 := by decide +kernel
private theorem decode_coordinates_10 : decode (coordinates 10) = 10 := by decide +kernel
private theorem decode_coordinates_11 : decode (coordinates 11) = 11 := by decide +kernel
private theorem decode_coordinates_12 : decode (coordinates 12) = 12 := by decide +kernel
private theorem decode_coordinates_13 : decode (coordinates 13) = 13 := by decide +kernel
private theorem decode_coordinates_14 : decode (coordinates 14) = 14 := by decide +kernel
private theorem decode_coordinates_15 : decode (coordinates 15) = 15 := by decide +kernel
private theorem decode_coordinates_16 : decode (coordinates 16) = 16 := by decide +kernel
private theorem decode_coordinates_17 : decode (coordinates 17) = 17 := by decide +kernel
private theorem decode_coordinates_18 : decode (coordinates 18) = 18 := by decide +kernel
private theorem decode_coordinates_19 : decode (coordinates 19) = 19 := by decide +kernel
private theorem decode_coordinates_20 : decode (coordinates 20) = 20 := by decide +kernel
private theorem decode_coordinates_21 : decode (coordinates 21) = 21 := by decide +kernel
private theorem decode_coordinates_22 : decode (coordinates 22) = 22 := by decide +kernel
private theorem decode_coordinates_23 : decode (coordinates 23) = 23 := by decide +kernel
private theorem decode_coordinates_24 : decode (coordinates 24) = 24 := by decide +kernel
private theorem decode_coordinates_25 : decode (coordinates 25) = 25 := by decide +kernel
private theorem decode_coordinates_26 : decode (coordinates 26) = 26 := by decide +kernel
private theorem decode_coordinates_27 : decode (coordinates 27) = 27 := by decide +kernel
private theorem decode_coordinates_28 : decode (coordinates 28) = 28 := by decide +kernel
private theorem decode_coordinates_29 : decode (coordinates 29) = 29 := by decide +kernel
private theorem decode_coordinates_30 : decode (coordinates 30) = 30 := by decide +kernel
private theorem decode_coordinates_31 : decode (coordinates 31) = 31 := by decide +kernel
private theorem decode_coordinates_32 : decode (coordinates 32) = 32 := by decide +kernel
private theorem decode_coordinates_33 : decode (coordinates 33) = 33 := by decide +kernel
private theorem decode_coordinates_34 : decode (coordinates 34) = 34 := by decide +kernel
private theorem decode_coordinates_35 : decode (coordinates 35) = 35 := by decide +kernel
private theorem decode_coordinates_36 : decode (coordinates 36) = 36 := by decide +kernel
private theorem decode_coordinates_37 : decode (coordinates 37) = 37 := by decide +kernel
private theorem decode_coordinates_38 : decode (coordinates 38) = 38 := by decide +kernel
private theorem decode_coordinates_39 : decode (coordinates 39) = 39 := by decide +kernel
private theorem decode_coordinates_40 : decode (coordinates 40) = 40 := by decide +kernel
private theorem decode_coordinates_41 : decode (coordinates 41) = 41 := by decide +kernel
private theorem decode_coordinates_42 : decode (coordinates 42) = 42 := by decide +kernel
private theorem decode_coordinates_43 : decode (coordinates 43) = 43 := by decide +kernel
private theorem decode_coordinates_44 : decode (coordinates 44) = 44 := by decide +kernel
private theorem decode_coordinates_45 : decode (coordinates 45) = 45 := by decide +kernel
private theorem decode_coordinates_46 : decode (coordinates 46) = 46 := by decide +kernel
private theorem decode_coordinates_47 : decode (coordinates 47) = 47 := by decide +kernel
private theorem decode_coordinates_48 : decode (coordinates 48) = 48 := by decide +kernel
private theorem decode_coordinates_49 : decode (coordinates 49) = 49 := by decide +kernel
private theorem decode_coordinates_50 : decode (coordinates 50) = 50 := by decide +kernel
private theorem decode_coordinates_51 : decode (coordinates 51) = 51 := by decide +kernel
private theorem decode_coordinates_52 : decode (coordinates 52) = 52 := by decide +kernel
private theorem decode_coordinates_53 : decode (coordinates 53) = 53 := by decide +kernel
private theorem decode_coordinates_54 : decode (coordinates 54) = 54 := by decide +kernel
private theorem decode_coordinates_55 : decode (coordinates 55) = 55 := by decide +kernel
theorem decode_coordinates : ∀ a : Weight, decode (coordinates a) = a := by
  intro a
  fin_cases a
  · exact decode_coordinates_0
  · exact decode_coordinates_1
  · exact decode_coordinates_2
  · exact decode_coordinates_3
  · exact decode_coordinates_4
  · exact decode_coordinates_5
  · exact decode_coordinates_6
  · exact decode_coordinates_7
  · exact decode_coordinates_8
  · exact decode_coordinates_9
  · exact decode_coordinates_10
  · exact decode_coordinates_11
  · exact decode_coordinates_12
  · exact decode_coordinates_13
  · exact decode_coordinates_14
  · exact decode_coordinates_15
  · exact decode_coordinates_16
  · exact decode_coordinates_17
  · exact decode_coordinates_18
  · exact decode_coordinates_19
  · exact decode_coordinates_20
  · exact decode_coordinates_21
  · exact decode_coordinates_22
  · exact decode_coordinates_23
  · exact decode_coordinates_24
  · exact decode_coordinates_25
  · exact decode_coordinates_26
  · exact decode_coordinates_27
  · exact decode_coordinates_28
  · exact decode_coordinates_29
  · exact decode_coordinates_30
  · exact decode_coordinates_31
  · exact decode_coordinates_32
  · exact decode_coordinates_33
  · exact decode_coordinates_34
  · exact decode_coordinates_35
  · exact decode_coordinates_36
  · exact decode_coordinates_37
  · exact decode_coordinates_38
  · exact decode_coordinates_39
  · exact decode_coordinates_40
  · exact decode_coordinates_41
  · exact decode_coordinates_42
  · exact decode_coordinates_43
  · exact decode_coordinates_44
  · exact decode_coordinates_45
  · exact decode_coordinates_46
  · exact decode_coordinates_47
  · exact decode_coordinates_48
  · exact decode_coordinates_49
  · exact decode_coordinates_50
  · exact decode_coordinates_51
  · exact decode_coordinates_52
  · exact decode_coordinates_53
  · exact decode_coordinates_54
  · exact decode_coordinates_55
theorem coordinates_injective : Function.Injective coordinates := Function.LeftInverse.injective decode_coordinates
theorem initial_coordinates : coordinates 0 = Pi.single selectedNode 1 := by decide +kernel

end Atlas.Chevalley.E7MinusculeTable
