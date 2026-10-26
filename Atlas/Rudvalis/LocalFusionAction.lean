import Atlas.Rudvalis.LocalFusionElement
import Atlas.Rudvalis.CoordinateCrossAction

set_option maxRecDepth 16384
namespace Atlas.Rudvalis

noncomputable def localFusionSourceCoordinate (c : Fin 3) : Coordinate :=
  seedCoordinateEquiv ((localFusionSource c).1,signedPositionIndex (localFusionSource c).2)
noncomputable def localFusionTargetCoordinate (c : Fin 3) : Coordinate :=
  seedCoordinateEquiv ((localFusionTarget c).1,signedPositionIndex (localFusionTarget c).2)

 theorem localFusionSource_axis (c : Fin 3) :
    originalFrame (localFusionSource c)=coordinateMinimum (localFusionSourceCoordinate c) := by
  rw [originalFrame_signed_axis]
  have h : (localFusionSource c).2≠0 := by decide +kernel +revert
  rw [if_neg h]
  rfl
 theorem localFusionTarget_axis (c : Fin 3) :
    originalFrame (localFusionTarget c)=coordinateMinimum (localFusionTargetCoordinate c) := by
  rw [originalFrame_signed_axis]
  have h : (localFusionTarget c).2≠0 := by decide +kernel +revert
  rw [if_neg h]
  rfl

 theorem localFusionT_coordinate_columns (c : Fin 3) :
    localFusionT.val (coordinateMinimum (localFusionSourceCoordinate c))=
      -coordinateMinimum (localFusionTargetCoordinate c) := by
  rw [←localFusionSource_axis,←localFusionTarget_axis]
  exact localFusionT_columns c

theorem gaussian_coordinateCross_of_negative (g : gaussianLatticeGroup) (i j : Coordinate)
    (h : g.val (coordinateMinimum i)= -coordinateMinimum j) :
    g • coordinateCross i=coordinateCross j := by
  have hv : g • coordinateShellLift (i,true)=coordinateShellLift (j,false) := by
    apply Subtype.ext
    apply Subtype.ext
    exact h
  change minimalCross (g • coordinateShellLift (i,true))=_
  rw [hv,coordinateCross_negative]

theorem localFusionT_cross_action (c : Fin 3) :
    localFusionT • coordinateCross (localFusionSourceCoordinate c)=
      coordinateCross (localFusionTargetCoordinate c) :=
  gaussian_coordinateCross_of_negative _ _ _ (localFusionT_coordinate_columns c)

 theorem localFusionT_fixes_first :
    localFusionT • coordinateCross (localFusionSourceCoordinate 0)=
      coordinateCross (localFusionSourceCoordinate 0) := by
  simpa [localFusionSourceCoordinate,localFusionTargetCoordinate,localFusionSource,localFusionTarget]
    using localFusionT_cross_action 0

 theorem localFusionT_fixes_second :
    localFusionT • coordinateCross (localFusionSourceCoordinate 1)=
      coordinateCross (localFusionSourceCoordinate 1) := by
  simpa [localFusionSourceCoordinate,localFusionTargetCoordinate,localFusionSource,localFusionTarget]
    using localFusionT_cross_action 1

 theorem localFusionT_pair_stabilizer :
    localFusionT∈MulAction.stabilizer gaussianLatticeGroup (coordinateCross (localFusionSourceCoordinate 0)) ⊓
      MulAction.stabilizer gaussianLatticeGroup (coordinateCross (localFusionSourceCoordinate 1)) :=
  ⟨localFusionT_fixes_first,localFusionT_fixes_second⟩

 theorem localFusion_source_same_row :
    (localFusionSourceCoordinate 0).1=(localFusionSourceCoordinate 2).1 := rfl
 theorem localFusion_target_other_row :
    (localFusionSourceCoordinate 0).1≠(localFusionTargetCoordinate 2).1 := by decide +kernel

noncomputable def generatedLocalFusionT : generatedGaussianGroup :=
  ⟨localFusionT,localFusionT_mem_generated⟩

theorem localFusionT_third_vector :
    localFusionT.val (originalFrame (0,4))= -rationalI (originalFrame (4,6)) := by
  have hi : rationalI (originalFrame (4,6))=originalFrame (4,7) := codeUnit_originalFrame 4 4 6
  rw [hi]
  have h := localFusionT_columns 2
  change localFusionT.val (originalFrame (0,4))= -originalFrame (4,7) at h
  exact h

end Atlas.Rudvalis

