import Atlas.LinearGroups.Chevalley.Integral.E6MinusculeTable.Data

/-! E6 minuscule certificate component: Injectivity. -/
namespace Atlas.Chevalley.E6MinusculeTable
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
theorem coordinates_injective : Function.Injective coordinates := Function.LeftInverse.injective decode_coordinates
theorem initial_coordinates : coordinates 0 = Pi.single selectedNode 1 := by decide +kernel

end Atlas.Chevalley.E6MinusculeTable
