import Atlas.LinearGroups.Chevalley.Integral.E6MinusculeTable.Data

/-! E6 minuscule certificate component: SimpleReflections. -/
namespace Atlas.Chevalley.E6MinusculeTable
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem simple_reflection_coordinates_0 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 0) = reflectSimple i (coordinates 0) := by decide +kernel
private theorem simple_reflection_coordinates_1 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 1) = reflectSimple i (coordinates 1) := by decide +kernel
private theorem simple_reflection_coordinates_2 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 2) = reflectSimple i (coordinates 2) := by decide +kernel
private theorem simple_reflection_coordinates_3 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 3) = reflectSimple i (coordinates 3) := by decide +kernel
private theorem simple_reflection_coordinates_4 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 4) = reflectSimple i (coordinates 4) := by decide +kernel
private theorem simple_reflection_coordinates_5 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 5) = reflectSimple i (coordinates 5) := by decide +kernel
private theorem simple_reflection_coordinates_6 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 6) = reflectSimple i (coordinates 6) := by decide +kernel
private theorem simple_reflection_coordinates_7 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 7) = reflectSimple i (coordinates 7) := by decide +kernel
private theorem simple_reflection_coordinates_8 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 8) = reflectSimple i (coordinates 8) := by decide +kernel
private theorem simple_reflection_coordinates_9 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 9) = reflectSimple i (coordinates 9) := by decide +kernel
private theorem simple_reflection_coordinates_10 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 10) = reflectSimple i (coordinates 10) := by decide +kernel
private theorem simple_reflection_coordinates_11 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 11) = reflectSimple i (coordinates 11) := by decide +kernel
private theorem simple_reflection_coordinates_12 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 12) = reflectSimple i (coordinates 12) := by decide +kernel
private theorem simple_reflection_coordinates_13 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 13) = reflectSimple i (coordinates 13) := by decide +kernel
private theorem simple_reflection_coordinates_14 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 14) = reflectSimple i (coordinates 14) := by decide +kernel
private theorem simple_reflection_coordinates_15 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 15) = reflectSimple i (coordinates 15) := by decide +kernel
private theorem simple_reflection_coordinates_16 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 16) = reflectSimple i (coordinates 16) := by decide +kernel
private theorem simple_reflection_coordinates_17 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 17) = reflectSimple i (coordinates 17) := by decide +kernel
private theorem simple_reflection_coordinates_18 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 18) = reflectSimple i (coordinates 18) := by decide +kernel
private theorem simple_reflection_coordinates_19 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 19) = reflectSimple i (coordinates 19) := by decide +kernel
private theorem simple_reflection_coordinates_20 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 20) = reflectSimple i (coordinates 20) := by decide +kernel
private theorem simple_reflection_coordinates_21 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 21) = reflectSimple i (coordinates 21) := by decide +kernel
private theorem simple_reflection_coordinates_22 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 22) = reflectSimple i (coordinates 22) := by decide +kernel
private theorem simple_reflection_coordinates_23 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 23) = reflectSimple i (coordinates 23) := by decide +kernel
private theorem simple_reflection_coordinates_24 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 24) = reflectSimple i (coordinates 24) := by decide +kernel
private theorem simple_reflection_coordinates_25 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 25) = reflectSimple i (coordinates 25) := by decide +kernel
private theorem simple_reflection_coordinates_26 : ∀ i : Fin 6, coordinates (simpleReflectionIndex i 26) = reflectSimple i (coordinates 26) := by decide +kernel
theorem simple_reflection_coordinates : ∀ a : Weight, ∀ i : Fin 6, coordinates (simpleReflectionIndex i a) = reflectSimple i (coordinates a) := by
  intro a
  fin_cases a
  · exact simple_reflection_coordinates_0
  · exact simple_reflection_coordinates_1
  · exact simple_reflection_coordinates_2
  · exact simple_reflection_coordinates_3
  · exact simple_reflection_coordinates_4
  · exact simple_reflection_coordinates_5
  · exact simple_reflection_coordinates_6
  · exact simple_reflection_coordinates_7
  · exact simple_reflection_coordinates_8
  · exact simple_reflection_coordinates_9
  · exact simple_reflection_coordinates_10
  · exact simple_reflection_coordinates_11
  · exact simple_reflection_coordinates_12
  · exact simple_reflection_coordinates_13
  · exact simple_reflection_coordinates_14
  · exact simple_reflection_coordinates_15
  · exact simple_reflection_coordinates_16
  · exact simple_reflection_coordinates_17
  · exact simple_reflection_coordinates_18
  · exact simple_reflection_coordinates_19
  · exact simple_reflection_coordinates_20
  · exact simple_reflection_coordinates_21
  · exact simple_reflection_coordinates_22
  · exact simple_reflection_coordinates_23
  · exact simple_reflection_coordinates_24
  · exact simple_reflection_coordinates_25
  · exact simple_reflection_coordinates_26

end Atlas.Chevalley.E6MinusculeTable
