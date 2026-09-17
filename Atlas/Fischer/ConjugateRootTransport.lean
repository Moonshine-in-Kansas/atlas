import Atlas.Fischer.RootCovariance
import Atlas.Fischer.RootTensorTheorem

noncomputable section
namespace Atlas.Fischer

/-- Root equations transport through an actual conjugate-linear antiunitary
algebra equivalence; the real constants9 and10 are fixed by conjugation. -/
theorem isRoot_conjugate_transport (g : Coordinates ≃ₛₗ[starRingEnd Scalar] Coordinates)
    (hp : ∀ x y, product (g x) (g y)=g (product x y))
    (hh : ∀ x y, hermitian (g x) (g y)=star (hermitian x y))
    (r : Coordinates) (hr : IsRoot r) : IsRoot (g r) := by
  constructor
  · rw [hh,hr.1]
    norm_num
  · rw [hp,hr.2,map_smulₛₗ]
    change star (10 : Scalar) • g r=10 • g r
    norm_num

/-- Antiunitarity of the root map transports by conjugation, independently of
membership in any finite root family. -/
theorem rootMapAntiunitary_conjugate_transport
    (g : Coordinates ≃ₛₗ[starRingEnd Scalar] Coordinates)
    (hp : ∀ x y, product (g x) (g y)=g (product x y))
    (hh : ∀ x y, hermitian (g x) (g y)=star (hermitian x y))
    (r : Coordinates) (ha : RootMapAntiunitary r) : RootMapAntiunitary (g r) := by
  intro x y
  obtain ⟨u,rfl⟩ := g.surjective x
  obtain ⟨v,rfl⟩ := g.surjective y
  rw [rootMap_covariance_conjugate g hp hh,rootMap_covariance_conjugate g hp hh,
    hh,ha,hh]

end Atlas.Fischer
