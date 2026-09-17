import Atlas.Fischer.DuadProductRoots
import Atlas.Fischer.DuadCharacterDecomposition
import Atlas.Fischer.DuadCocode
import Atlas.Fischer.OctadicCocodeAction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual restricted cocode character decomposes into its two octadic
restrictions under the retained direct-sum equivalence. -/
theorem duadCharacterEquiv_cocode (p : Finset Omega) (hp : p.card=2)
    (F G : Octad) (hFG : F.val ∩ G.val=p) (d : Cocode) :
    duadCharacterEquiv p hp F G hFG
      (octadCocodeRestriction F d,octadCocodeRestriction G d)=duadCocodeRestriction p d := by
  apply LinearMap.ext
  intro c
  obtain ⟨⟨x,y⟩,rfl⟩ := (duadOctadSumEquiv p hp F G hFG).surjective c
  rw [duadCharacterEquiv_on_sum]
  change cocodePairing x.val d+cocodePairing y.val d=cocodePairing (x.val+y.val) d
  exact (map_add (cocodeDualEquiv d) x.val y.val).symm

/-- Cocode covariance of the actual product of two calibrated octadic roots. -/
theorem parkerCocodeAction_duadOctadicProduct (d : Cocode) {F G : Octad}
    (Q : OctadCalibration F) (R : OctadCalibration G)
    (χ : OctadicCharacter F) (ψ : OctadicCharacter G) :
    parkerCoordinateAction (parkerCocodeStandard d) (duadOctadicProduct Q R χ ψ)=
      duadOctadicProduct Q R (χ+octadCocodeRestriction F d) (ψ+octadCocodeRestriction G d) := by
  rw [duadOctadicProduct,parkerCoordinateAction_product,
    parkerCocodeAction_octadicRoot,parkerCocodeAction_octadicRoot]
  rfl

end Atlas.Fischer
