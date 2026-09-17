import Atlas.Fischer.ParkerAlgebraRepresentation
import Atlas.Fischer.RootRays
import Atlas.Fischer.BasicRoots

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The Parker coordinate permutation fixes the sum of point axes. -/
theorem parkerCoordinateAction_axisSum (h : ParkerStandardGroup) :
    parkerCoordinateAction h axisSum=axisSum := by
  simp only [axisSum,map_sum,parkerCoordinateAction_u]
  exact Equiv.sum_comp (parkerStandardProjection h).val u

/-- The actual Parker representation permutes the actual basic roots. -/
theorem parkerCoordinateAction_basicAxis (h : ParkerStandardGroup) (i : Omega) :
    parkerCoordinateAction h (basicAxis i)=basicAxis ((parkerStandardProjection h).val i) := by
  have hs := parkerCoordinateAction_axisSum h
  rw [basicAxis_eq,map_sub,map_smulₛₗ,hs,parkerCoordinateAction_u,basicAxis_eq]
  change axisSum-scalarParityAut (parkerStandardParity h).toAdd 8 • _ = _
  rw [map_ofNat]

/-- Cubic scalars times Parker operators preserve the full marked basic frame. -/
theorem scalar_parker_basic_frame (a : Mu3) (h : ParkerStandardGroup) (i : Omega) :
    rootRay ((scalarAlgebraRepresentation a * parkerAlgebraRepresentation h).val (basicAxis i))=
      rootRay (basicAxis ((parkerStandardProjection h).val i)) := by
  change rootRay (a.val.val • parkerCoordinateAction h (basicAxis i))=_
  rw [parkerCoordinateAction_basicAxis]
  exact rootRay_phase _ _ ((mem_rootsOfUnity' _ _).mp a.property)

end Atlas.Fischer
