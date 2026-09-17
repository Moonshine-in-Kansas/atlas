import Atlas.Fischer.CountingShapeFibres
import Atlas.Fischer.CountingShapeCounts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
local instance countingShapeSumsSourceFintype : Fintype CountingSourceParameters := by
  classical
  infer_instance

/-- Sum any weights on geometric source shapes using actual parameter-fiber
sizes. This is not restricted to the later signed counting values. -/
theorem countingSourceShape_sum {R : Type*} [AddCommMonoid R]
    (f : CountingSourceShape → R) :
    (∑ t : CountingSourceParameters, f (countingSourceShape t)) =
      ∑ s : CountingSourceShape, countingShapeMultiplicity s • f s := by
  classical
  have hc (s : CountingSourceShape) :
      Fintype.card {t : CountingSourceParameters // countingSourceShape t=s} =
        countingShapeMultiplicity s := by
    rw [← Nat.card_eq_fintype_card]
    exact countingSourceShape_fiber_card s
  rw [← Fintype.sum_fiberwise' countingSourceShape]
  apply Finset.sum_congr rfl
  intro s _
  simp [hc]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem countingSourceShape_row_sum (trio : Bool) (r : Fin 14) :
    (∑ t : CountingSourceParameters,
      if countingShapeAdmissible (countingSourceShape t) ∧
        countingShapeRow trio (countingSourceShape t)=r then (1 : ℕ) else 0) =
      countingShapeExpectedMultiplicity trio r := by
  classical
  rw [countingSourceShape_sum (fun s =>
    if countingShapeAdmissible s ∧ countingShapeRow trio s=r then (1 : ℕ) else 0)]
  calc
    _ = ∑ s : CountingSourceShape,
        if countingShapeAdmissible s ∧ countingShapeRow trio s=r
          then countingShapeMultiplicity s else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases h : countingShapeAdmissible s ∧ countingShapeRow trio s=r <;> simp [h]
    _ = _ := countingShape_weighted_row_counts trio r

end Atlas.Fischer
