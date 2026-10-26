import Atlas.LinearGroups.Chevalley.RootData.F4Table.Data

/-! F4 root certificate component: Injectivity. -/
namespace Atlas.Chevalley.F4Table
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem coordinates_injective : Function.Injective coordinates := by
  intro a b h
  apply Atlas.F4.RootData.coordinates_injective
  rw [Atlas.F4.RootData.simpleCoefficients_reconstruct a,
    Atlas.F4.RootData.simpleCoefficients_reconstruct b]
  change (∑ i, coordinates a i • Atlas.F4.RootData.coordinates (Atlas.F4.RootData.simpleRoot i)) =
    ∑ i, coordinates b i • Atlas.F4.RootData.coordinates (Atlas.F4.RootData.simpleRoot i)
  rw [h]
private theorem dual_decode_0 : dualDecode (dualCoordinates 0) = 0 := by decide +kernel
private theorem dual_decode_1 : dualDecode (dualCoordinates 1) = 1 := by decide +kernel
private theorem dual_decode_2 : dualDecode (dualCoordinates 2) = 2 := by decide +kernel
private theorem dual_decode_3 : dualDecode (dualCoordinates 3) = 3 := by decide +kernel
private theorem dual_decode_4 : dualDecode (dualCoordinates 4) = 4 := by decide +kernel
private theorem dual_decode_5 : dualDecode (dualCoordinates 5) = 5 := by decide +kernel
private theorem dual_decode_6 : dualDecode (dualCoordinates 6) = 6 := by decide +kernel
private theorem dual_decode_7 : dualDecode (dualCoordinates 7) = 7 := by decide +kernel
private theorem dual_decode_8 : dualDecode (dualCoordinates 8) = 8 := by decide +kernel
private theorem dual_decode_9 : dualDecode (dualCoordinates 9) = 9 := by decide +kernel
private theorem dual_decode_10 : dualDecode (dualCoordinates 10) = 10 := by decide +kernel
private theorem dual_decode_11 : dualDecode (dualCoordinates 11) = 11 := by decide +kernel
private theorem dual_decode_12 : dualDecode (dualCoordinates 12) = 12 := by decide +kernel
private theorem dual_decode_13 : dualDecode (dualCoordinates 13) = 13 := by decide +kernel
private theorem dual_decode_14 : dualDecode (dualCoordinates 14) = 14 := by decide +kernel
private theorem dual_decode_15 : dualDecode (dualCoordinates 15) = 15 := by decide +kernel
private theorem dual_decode_16 : dualDecode (dualCoordinates 16) = 16 := by decide +kernel
private theorem dual_decode_17 : dualDecode (dualCoordinates 17) = 17 := by decide +kernel
private theorem dual_decode_18 : dualDecode (dualCoordinates 18) = 18 := by decide +kernel
private theorem dual_decode_19 : dualDecode (dualCoordinates 19) = 19 := by decide +kernel
private theorem dual_decode_20 : dualDecode (dualCoordinates 20) = 20 := by decide +kernel
private theorem dual_decode_21 : dualDecode (dualCoordinates 21) = 21 := by decide +kernel
private theorem dual_decode_22 : dualDecode (dualCoordinates 22) = 22 := by decide +kernel
private theorem dual_decode_23 : dualDecode (dualCoordinates 23) = 23 := by decide +kernel
private theorem dual_decode_24 : dualDecode (dualCoordinates 24) = 24 := by decide +kernel
private theorem dual_decode_25 : dualDecode (dualCoordinates 25) = 25 := by decide +kernel
private theorem dual_decode_26 : dualDecode (dualCoordinates 26) = 26 := by decide +kernel
private theorem dual_decode_27 : dualDecode (dualCoordinates 27) = 27 := by decide +kernel
private theorem dual_decode_28 : dualDecode (dualCoordinates 28) = 28 := by decide +kernel
private theorem dual_decode_29 : dualDecode (dualCoordinates 29) = 29 := by decide +kernel
private theorem dual_decode_30 : dualDecode (dualCoordinates 30) = 30 := by decide +kernel
private theorem dual_decode_31 : dualDecode (dualCoordinates 31) = 31 := by decide +kernel
private theorem dual_decode_32 : dualDecode (dualCoordinates 32) = 32 := by decide +kernel
private theorem dual_decode_33 : dualDecode (dualCoordinates 33) = 33 := by decide +kernel
private theorem dual_decode_34 : dualDecode (dualCoordinates 34) = 34 := by decide +kernel
private theorem dual_decode_35 : dualDecode (dualCoordinates 35) = 35 := by decide +kernel
private theorem dual_decode_36 : dualDecode (dualCoordinates 36) = 36 := by decide +kernel
private theorem dual_decode_37 : dualDecode (dualCoordinates 37) = 37 := by decide +kernel
private theorem dual_decode_38 : dualDecode (dualCoordinates 38) = 38 := by decide +kernel
private theorem dual_decode_39 : dualDecode (dualCoordinates 39) = 39 := by decide +kernel
private theorem dual_decode_40 : dualDecode (dualCoordinates 40) = 40 := by decide +kernel
private theorem dual_decode_41 : dualDecode (dualCoordinates 41) = 41 := by decide +kernel
private theorem dual_decode_42 : dualDecode (dualCoordinates 42) = 42 := by decide +kernel
private theorem dual_decode_43 : dualDecode (dualCoordinates 43) = 43 := by decide +kernel
private theorem dual_decode_44 : dualDecode (dualCoordinates 44) = 44 := by decide +kernel
private theorem dual_decode_45 : dualDecode (dualCoordinates 45) = 45 := by decide +kernel
private theorem dual_decode_46 : dualDecode (dualCoordinates 46) = 46 := by decide +kernel
private theorem dual_decode_47 : dualDecode (dualCoordinates 47) = 47 := by decide +kernel
theorem dual_decode : ∀ a : Root, dualDecode (dualCoordinates a) = a := by
  intro a
  fin_cases a
  · exact dual_decode_0
  · exact dual_decode_1
  · exact dual_decode_2
  · exact dual_decode_3
  · exact dual_decode_4
  · exact dual_decode_5
  · exact dual_decode_6
  · exact dual_decode_7
  · exact dual_decode_8
  · exact dual_decode_9
  · exact dual_decode_10
  · exact dual_decode_11
  · exact dual_decode_12
  · exact dual_decode_13
  · exact dual_decode_14
  · exact dual_decode_15
  · exact dual_decode_16
  · exact dual_decode_17
  · exact dual_decode_18
  · exact dual_decode_19
  · exact dual_decode_20
  · exact dual_decode_21
  · exact dual_decode_22
  · exact dual_decode_23
  · exact dual_decode_24
  · exact dual_decode_25
  · exact dual_decode_26
  · exact dual_decode_27
  · exact dual_decode_28
  · exact dual_decode_29
  · exact dual_decode_30
  · exact dual_decode_31
  · exact dual_decode_32
  · exact dual_decode_33
  · exact dual_decode_34
  · exact dual_decode_35
  · exact dual_decode_36
  · exact dual_decode_37
  · exact dual_decode_38
  · exact dual_decode_39
  · exact dual_decode_40
  · exact dual_decode_41
  · exact dual_decode_42
  · exact dual_decode_43
  · exact dual_decode_44
  · exact dual_decode_45
  · exact dual_decode_46
  · exact dual_decode_47
theorem dualCoordinates_injective : Function.Injective dualCoordinates := Function.LeftInverse.injective dual_decode

end Atlas.Chevalley.F4Table
