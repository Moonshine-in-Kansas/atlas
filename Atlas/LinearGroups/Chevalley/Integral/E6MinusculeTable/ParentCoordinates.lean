import Atlas.LinearGroups.Chevalley.Integral.E6MinusculeTable.Data

/-! E6 minuscule certificate component: ParentCoordinates. -/
namespace Atlas.Chevalley.E6MinusculeTable
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem parent_coordinates_0 : (0 : Weight) ≠ 0 → coordinates 0 = reflectSimple (lastStep 0) (coordinates (parent 0)) := by decide +kernel
private theorem parent_coordinates_1 : (1 : Weight) ≠ 0 → coordinates 1 = reflectSimple (lastStep 1) (coordinates (parent 1)) := by decide +kernel
private theorem parent_coordinates_2 : (2 : Weight) ≠ 0 → coordinates 2 = reflectSimple (lastStep 2) (coordinates (parent 2)) := by decide +kernel
private theorem parent_coordinates_3 : (3 : Weight) ≠ 0 → coordinates 3 = reflectSimple (lastStep 3) (coordinates (parent 3)) := by decide +kernel
private theorem parent_coordinates_4 : (4 : Weight) ≠ 0 → coordinates 4 = reflectSimple (lastStep 4) (coordinates (parent 4)) := by decide +kernel
private theorem parent_coordinates_5 : (5 : Weight) ≠ 0 → coordinates 5 = reflectSimple (lastStep 5) (coordinates (parent 5)) := by decide +kernel
private theorem parent_coordinates_6 : (6 : Weight) ≠ 0 → coordinates 6 = reflectSimple (lastStep 6) (coordinates (parent 6)) := by decide +kernel
private theorem parent_coordinates_7 : (7 : Weight) ≠ 0 → coordinates 7 = reflectSimple (lastStep 7) (coordinates (parent 7)) := by decide +kernel
private theorem parent_coordinates_8 : (8 : Weight) ≠ 0 → coordinates 8 = reflectSimple (lastStep 8) (coordinates (parent 8)) := by decide +kernel
private theorem parent_coordinates_9 : (9 : Weight) ≠ 0 → coordinates 9 = reflectSimple (lastStep 9) (coordinates (parent 9)) := by decide +kernel
private theorem parent_coordinates_10 : (10 : Weight) ≠ 0 → coordinates 10 = reflectSimple (lastStep 10) (coordinates (parent 10)) := by decide +kernel
private theorem parent_coordinates_11 : (11 : Weight) ≠ 0 → coordinates 11 = reflectSimple (lastStep 11) (coordinates (parent 11)) := by decide +kernel
private theorem parent_coordinates_12 : (12 : Weight) ≠ 0 → coordinates 12 = reflectSimple (lastStep 12) (coordinates (parent 12)) := by decide +kernel
private theorem parent_coordinates_13 : (13 : Weight) ≠ 0 → coordinates 13 = reflectSimple (lastStep 13) (coordinates (parent 13)) := by decide +kernel
private theorem parent_coordinates_14 : (14 : Weight) ≠ 0 → coordinates 14 = reflectSimple (lastStep 14) (coordinates (parent 14)) := by decide +kernel
private theorem parent_coordinates_15 : (15 : Weight) ≠ 0 → coordinates 15 = reflectSimple (lastStep 15) (coordinates (parent 15)) := by decide +kernel
private theorem parent_coordinates_16 : (16 : Weight) ≠ 0 → coordinates 16 = reflectSimple (lastStep 16) (coordinates (parent 16)) := by decide +kernel
private theorem parent_coordinates_17 : (17 : Weight) ≠ 0 → coordinates 17 = reflectSimple (lastStep 17) (coordinates (parent 17)) := by decide +kernel
private theorem parent_coordinates_18 : (18 : Weight) ≠ 0 → coordinates 18 = reflectSimple (lastStep 18) (coordinates (parent 18)) := by decide +kernel
private theorem parent_coordinates_19 : (19 : Weight) ≠ 0 → coordinates 19 = reflectSimple (lastStep 19) (coordinates (parent 19)) := by decide +kernel
private theorem parent_coordinates_20 : (20 : Weight) ≠ 0 → coordinates 20 = reflectSimple (lastStep 20) (coordinates (parent 20)) := by decide +kernel
private theorem parent_coordinates_21 : (21 : Weight) ≠ 0 → coordinates 21 = reflectSimple (lastStep 21) (coordinates (parent 21)) := by decide +kernel
private theorem parent_coordinates_22 : (22 : Weight) ≠ 0 → coordinates 22 = reflectSimple (lastStep 22) (coordinates (parent 22)) := by decide +kernel
private theorem parent_coordinates_23 : (23 : Weight) ≠ 0 → coordinates 23 = reflectSimple (lastStep 23) (coordinates (parent 23)) := by decide +kernel
private theorem parent_coordinates_24 : (24 : Weight) ≠ 0 → coordinates 24 = reflectSimple (lastStep 24) (coordinates (parent 24)) := by decide +kernel
private theorem parent_coordinates_25 : (25 : Weight) ≠ 0 → coordinates 25 = reflectSimple (lastStep 25) (coordinates (parent 25)) := by decide +kernel
private theorem parent_coordinates_26 : (26 : Weight) ≠ 0 → coordinates 26 = reflectSimple (lastStep 26) (coordinates (parent 26)) := by decide +kernel
theorem parent_coordinates : ∀ a : Weight, a ≠ 0 → coordinates a = reflectSimple (lastStep a) (coordinates (parent a)) := by
  intro a
  fin_cases a
  · exact parent_coordinates_0
  · exact parent_coordinates_1
  · exact parent_coordinates_2
  · exact parent_coordinates_3
  · exact parent_coordinates_4
  · exact parent_coordinates_5
  · exact parent_coordinates_6
  · exact parent_coordinates_7
  · exact parent_coordinates_8
  · exact parent_coordinates_9
  · exact parent_coordinates_10
  · exact parent_coordinates_11
  · exact parent_coordinates_12
  · exact parent_coordinates_13
  · exact parent_coordinates_14
  · exact parent_coordinates_15
  · exact parent_coordinates_16
  · exact parent_coordinates_17
  · exact parent_coordinates_18
  · exact parent_coordinates_19
  · exact parent_coordinates_20
  · exact parent_coordinates_21
  · exact parent_coordinates_22
  · exact parent_coordinates_23
  · exact parent_coordinates_24
  · exact parent_coordinates_25
  · exact parent_coordinates_26

end Atlas.Chevalley.E6MinusculeTable
