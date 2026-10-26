import Atlas.Rudvalis.LocalFusionAction
import Atlas.Rudvalis.GaussianLocalFusionObstruction

namespace Atlas.Rudvalis

theorem localFusion_third_source_row :
    coordinateCross (localFusionSourceCoordinate 2)∈coordinateRowFrame (localFusionSourceCoordinate 0).1 := by
  refine ⟨(localFusionSourceCoordinate 2).2,?_⟩
  exact congrArg coordinateCross (Prod.ext localFusion_source_same_row rfl)

theorem localFusion_third_target_not_row :
    coordinateCross (localFusionTargetCoordinate 2)∉coordinateRowFrame (localFusionSourceCoordinate 0).1 := by
  rintro ⟨x,hx⟩
  exact localFusion_target_other_row (coordinateCross_row_of_eq (i:=((localFusionSourceCoordinate 0).1,x)) (j:=localFusionTargetCoordinate 2) hx)

theorem localFusionT_not_codeGroup : localFusionT∉Set.range codeGaussianHom := by
  rintro ⟨g,hg⟩
  have hfix : g • coordinateCross (localFusionSourceCoordinate 0)=
      coordinateCross (localFusionSourceCoordinate 0) := by
    rw [←codeGaussianHom_cross,hg]
    exact localFusionT_fixes_first
  let b : MulAction.stabilizer codeGroup (coordinateCross (localFusionSourceCoordinate 0)) := ⟨g,hfix⟩
  have hh := coordinateCross_stabilizer_row_mem
    (localFusionSourceCoordinate 0).1 (localFusionSourceCoordinate 0).2 b
    (coordinateCross (localFusionSourceCoordinate 2)) localFusion_third_source_row
  change g • coordinateCross (localFusionSourceCoordinate 2)∈
    coordinateRowFrame (localFusionSourceCoordinate 0).1 at hh
  rw [←codeGaussianHom_cross,hg,localFusionT_cross_action] at hh
  exact localFusion_third_target_not_row hh

/-- Every point-fixing subgroup containing the actual fusion word escapes the
27-point coordinate-frame complement orbit. -/
theorem localFusion_no_coordinate_complement_orbit (K : Subgroup gaussianLatticeGroup)
    (hfix : ∀g : K,g • coordinateCross (localFusionSourceCoordinate 0)=
      coordinateCross (localFusionSourceCoordinate 0)) (ht : localFusionT∈K) :
    MulAction.orbit K (coordinateCross (localFusionSourceCoordinate 2))≠
      coordinateFrame\{coordinateCross (localFusionSourceCoordinate 0)} := by
  apply gaussian_no_coordinate_complement_orbit K
    (localFusionSourceCoordinate 0).1 (localFusionSourceCoordinate 0).2
    (coordinateCross (localFusionSourceCoordinate 2))
    (coordinateCross (localFusionTargetCoordinate 2))
    localFusion_third_source_row localFusion_third_target_not_row hfix
  exact ⟨⟨localFusionT,ht⟩,localFusionT_cross_action 2⟩

end Atlas.Rudvalis
