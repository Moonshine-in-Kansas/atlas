import Atlas.Fischer.ReflectingFamilyMoments
import Atlas.Fischer.RootRayPreservationCriterion

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual constructed ray family determines algebra and metric. A
semilinear map permuting its normalized rays is automatically invertible. -/
theorem reflectingFamily_rayPermutation_criterion (b : Bit)
    (g : Coordinates →ₛₗ[(scalarParityAut b).toRingHom] Coordinates)
    (π : Equiv.Perm ReflectingRootParameter)
    (hg : ∀ j, rootRay (g (reflectingRootParameterVector j)) = reflectingRootParameterRay (π j)) :
    Function.Bijective g ∧
      (∀ x y, g (product x y) = product (g x) (g y)) ∧
      (∀ x y, hermitian (g x) (g y) = scalarParityAut b (hermitian x y)) :=
  reflectingRoot_rayPermutation_criterion reflectingRootParameterVector
    reflectingRootParameter_isReflectingRoot reflectingRootParameter_distinct_phases
    reflectingRootParameter_fintype_card b g π hg

end Atlas.Fischer
