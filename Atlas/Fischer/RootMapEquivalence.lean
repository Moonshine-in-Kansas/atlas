import Atlas.Fischer.RootMapSymmetry
import Atlas.Fischer.BasicCocodeComparison

noncomputable section
namespace Atlas.Fischer

/-- The actual root map is an invertible conjugate-linear map once antiunitarity is proved. -/
def rootMapEquivalence (r : Coordinates) (h : RootMapAntiunitary r) :
    Coordinates ≃ₛₗ[starRingEnd Scalar] Coordinates :=
  LinearEquiv.ofBijective (rootMapSemilinear r)
    (rootMap_involutive_of_antiunitary r h).bijective

theorem rootMapEquivalence_apply (r : Coordinates) (h : RootMapAntiunitary r)
    (x : Coordinates) : rootMapEquivalence r h x = rootMap r x := rfl

theorem rootMapEquivalence_symm_apply (r : Coordinates) (h : RootMapAntiunitary r)
    (x : Coordinates) : (rootMapEquivalence r h).symm x = rootMap r x := by
  apply (rootMapEquivalence r h).injective
  rw [LinearEquiv.apply_symm_apply, rootMapEquivalence_apply,
    rootMap_involutive_of_antiunitary r h]

theorem rootMapEquivalence_hermitian (r : Coordinates) (h : RootMapAntiunitary r)
    (x y : Coordinates) :
    hermitian (rootMapEquivalence r h x) (rootMapEquivalence r h y) =
      star (hermitian x y) := h x y

end Atlas.Fischer
