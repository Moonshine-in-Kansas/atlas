import Atlas.Rudvalis.LocalOrbitSizes
import Atlas.Rudvalis.HeavyCoordinateStabilizerOrbit

namespace Atlas.Rudvalis

theorem localReferenceCoordinate_eq : localFusionSourceCoordinate 0=(rowLabel 0,0) := by
  decide +kernel

theorem localReferenceCross_eq : localReferenceCross=coordinateCross (rowLabel 0,0) :=
  congrArg coordinateCross localReferenceCoordinate_eq

theorem reference_heavy_cross_transitive (v w : HeavyCrosses)
    (hv : CrossOrthogonal localReferenceCross (shellPieceCrossMap heavyShellPiece v))
    (hw : CrossOrthogonal localReferenceCross (shellPieceCrossMap heavyShellPiece w)) :
    ∃g : codeReferenceStabilizer,g.val • shellPieceCrossMap heavyShellPiece v=shellPieceCrossMap heavyShellPiece w := by
  rw [localReferenceCross_eq] at hv hw
  obtain ⟨g,hg,h⟩ := heavyCross_coordinate_stabilizer_transitive (rowLabel 0) v w hv hw
  refine ⟨⟨g,?_⟩,h⟩
  change g • localReferenceCross=localReferenceCross
  rw [localReferenceCross_eq]
  exact hg

end Atlas.Rudvalis
