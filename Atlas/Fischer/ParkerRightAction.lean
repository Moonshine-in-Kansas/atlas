import Atlas.Fischer.ParkerAlgebraRepresentation

namespace Atlas.Fischer
open Atlas.Codes

/-- The manuscript's right-action convention, recovered by inversion from
functional-composition left automorphisms of the actual Parker loop. -/
def parkerRightLoopAction (x : ParkerLoop) (g : ParkerStandardGroup) : ParkerLoop := g⁻¹.val x

noncomputable def parkerRightCoordinateAction (x : Coordinates) (g : ParkerStandardGroup) :
    Coordinates := parkerCoordinateAction g⁻¹ x

theorem parkerRightLoopAction_mul (x : ParkerLoop) (g h : ParkerStandardGroup) :
    parkerRightLoopAction x (g*h) = parkerRightLoopAction (parkerRightLoopAction x g) h := by
  unfold parkerRightLoopAction
  rw [mul_inv_rev]
  rfl

theorem parkerRightCoordinateAction_mul (x : Coordinates) (g h : ParkerStandardGroup) :
    parkerRightCoordinateAction x (g*h) =
      parkerRightCoordinateAction (parkerRightCoordinateAction x g) h := by
  change (g*h)⁻¹ • x = h⁻¹ • (g⁻¹ • x)
  rw [mul_inv_rev,mul_smul]

theorem parkerStandardParity_inv (g : ParkerStandardGroup) :
    parkerStandardParity g⁻¹ = parkerStandardParity g := by
  rw [map_inv]
  apply Multiplicative.toAdd.injective
  change -(parkerStandardParity g).toAdd = (parkerStandardParity g).toAdd
  exact CharTwo.neg_eq _

theorem parkerRightCoordinateAction_u (g : ParkerStandardGroup) (i : Omega) :
    parkerRightCoordinateAction (u i) g = u ((parkerStandardProjection g⁻¹).val i) :=
  parkerCoordinateAction_u g⁻¹ i

theorem parkerRightCoordinateAction_product (x y : Coordinates) (g : ParkerStandardGroup) :
    parkerRightCoordinateAction (product x y) g =
      product (parkerRightCoordinateAction x g) (parkerRightCoordinateAction y g) :=
  parkerCoordinateAction_product g⁻¹ x y

end Atlas.Fischer
