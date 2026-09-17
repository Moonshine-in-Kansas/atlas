import Atlas.Fischer.CountingSourceShapes

namespace Atlas.Fischer

/-- Complete source-row multiplicities, before the actual parameter-fiber
interpretation. There are only36 geometric source shapes. -/
def countingShapeExpectedMultiplicity (trio : Bool) : Fin 14 → ℕ :=
  if trio then ![0,0,0,0,0,0,0,2,4,24,8,48,96,128]
  else ![2,6,6,24,72,72,128,0,0,0,0,0,0,0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem countingShape_weighted_row_counts :
    ∀ (trio : Bool) (r : Fin 14),
      (∑ s : CountingSourceShape,
        if countingShapeAdmissible s ∧ countingShapeRow trio s=r
          then countingShapeMultiplicity s else 0) =
        countingShapeExpectedMultiplicity trio r := by
  decide

set_option maxRecDepth 4096 in
theorem countingShape_admissible_count :
    (Finset.univ.filter countingShapeAdmissible : Finset CountingSourceShape).card=23 := by
  decide

set_option maxRecDepth 4096 in
theorem countingShape_admissible_profile :
    ∀ s : CountingSourceShape,
      countingShapeAdmissible s ↔
        (∑ i ∈ countingTableD, countingShapeProfile s i)=0 ∨
          (∑ i ∈ countingTableD, countingShapeProfile s i)=4 := by
  decide

end Atlas.Fischer
