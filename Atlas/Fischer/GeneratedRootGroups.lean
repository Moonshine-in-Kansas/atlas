import Atlas.Fischer.SemilinearRayAction
import Atlas.Fischer.ReflectionCalculus

noncomputable section
namespace Atlas.Fischer

/-- The displayed representative determines an actual conjugate-linear algebra
involution; scalar phases are not identified at this level. -/
def displayedRootAutomorphism (t : ReflectingRootParameter) : SemilinearAlgebraAutomorphism :=
  reflectingRootAutomorphism (reflectingRootParameterVector t) (reflectingRootParameter_isReflectingRoot t)

/-- The algebra subgroup is generated only by the displayed root maps. -/
def rootGeneratedAlgebraGroup : Subgroup SemilinearAlgebraAutomorphism :=
  Subgroup.closure (Set.range displayedRootAutomorphism)

/-- The root involution induced on the actual ray set. -/
def displayedRootRayInvolution (t : ReflectingRootParameter) : Equiv.Perm DisplayedReflectingRay :=
  semilinearDisplayedRayAction (displayedRootAutomorphism t)

/-- The finite ray group is generated only by the derived root permutations;
no Parker subgroup or scalar kernel is assumed to lie in the generating set. -/
def rootGeneratedRayGroup : Subgroup (Equiv.Perm DisplayedReflectingRay) :=
  Subgroup.closure (Set.range displayedRootRayInvolution)

theorem displayedRootAutomorphism_mem (t : ReflectingRootParameter) :
    displayedRootAutomorphism t ∈ rootGeneratedAlgebraGroup := Subgroup.subset_closure ⟨t,rfl⟩

theorem displayedRootRayInvolution_mem (t : ReflectingRootParameter) :
    displayedRootRayInvolution t ∈ rootGeneratedRayGroup := Subgroup.subset_closure ⟨t,rfl⟩

theorem rootGeneratedAlgebraGroup_ray_image :
    rootGeneratedAlgebraGroup.map semilinearDisplayedRayAction=rootGeneratedRayGroup := by
  rw [rootGeneratedAlgebraGroup,MonoidHom.map_closure]
  congr 1
  exact Set.range_comp semilinearDisplayedRayAction displayedRootAutomorphism |>.symm

theorem displayedRootAutomorphism_square (t : ReflectingRootParameter) :
    displayedRootAutomorphism t ^ 2=1 :=
  rootAlgebraAutomorphism_square _ (reflectingRootParameter_isReflectingRoot t).1.1
    (reflectingRootParameter_isReflectingRoot t).1.2 (reflectingRootParameter_isReflectingRoot t).2.1

/-- This is the square identity; nontriviality and exact order are separate. -/
theorem displayedRootRayInvolution_square (t : ReflectingRootParameter) :
    displayedRootRayInvolution t ^ 2=1 := by
  rw [displayedRootRayInvolution,← map_pow,displayedRootAutomorphism_square,map_one]

end Atlas.Fischer
