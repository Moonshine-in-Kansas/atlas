import Atlas.Fischer.Roots

namespace Atlas.Fischer

/-- Covariance for an actual linear unitary product-preserving map. -/
theorem rootMap_covariance_linear (g : Coordinates ≃ₗ[Scalar] Coordinates)
    (hp : ∀ x y, product (g x) (g y) = g (product x y))
    (hh : ∀ x y, hermitian (g x) (g y) = hermitian x y)
    (r x : Coordinates) : rootMap (g r) (g x) = g (rootMap r x) := by
  rw [rootMap, hp, hh, rootMap, map_sub, map_smul]

/-- Covariance for an actual conjugate-linear antiunitary product-preserving map. -/
theorem rootMap_covariance_conjugate (g : Coordinates ≃ₛₗ[starRingEnd Scalar] Coordinates)
    (hp : ∀ x y, product (g x) (g y) = g (product x y))
    (hh : ∀ x y, hermitian (g x) (g y) = star (hermitian x y))
    (r x : Coordinates) : rootMap (g r) (g x) = g (rootMap r x) := by
  rw [rootMap, hp, hh, rootMap, map_sub, map_smulₛₗ]
  rfl

end Atlas.Fischer
