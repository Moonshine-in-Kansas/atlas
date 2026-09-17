import Atlas.Fischer.ParkerProductInvariance

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

theorem parkerCoordinateAction_basisProduct (e : ParkerStandardGroup) (i j : CoordinateIndex) :
    parkerCoordinateAction e (product (coordinateVector i) (coordinateVector j)) =
      product (parkerCoordinateAction e (coordinateVector i))
        (parkerCoordinateAction e (coordinateVector j)) := by
  cases i with
  | inl p =>
    cases j with
    | inl q =>
      change parkerCoordinateAction e (product (u p) (u q)) = _
      rw [product_u, parkerCoordinateAction_axisProduct]
      change axisBasisProduct _ _ = product (parkerCoordinateAction e (u p))
        (parkerCoordinateAction e (u q))
      rw [parkerCoordinateAction_u, parkerCoordinateAction_u, product_u]
    | inr O => exact parkerCoordinateAction_axisOctadProduct e p O
  | inr O =>
    cases j with
    | inl p =>
      rw [product_comm (coordinateVector (.inr O)) (coordinateVector (.inl p)),
        product_comm (parkerCoordinateAction e (coordinateVector (.inr O)))
          (parkerCoordinateAction e (coordinateVector (.inl p)))]
      exact parkerCoordinateAction_axisOctadProduct e p O
    | inr P => exact parkerCoordinateAction_octadProduct e O P

theorem coordinates_sum_basis (x : Coordinates) :
    (∑ i, x i • coordinateVector i) = x := by
  classical
  funext j
  simp [coordinateVector, Finset.sum_apply, Pi.single_apply, mul_ite]

theorem parkerCoordinateAction_sum_basis (e : ParkerStandardGroup) (x : Coordinates) :
    parkerCoordinateAction e x =
      ∑ i, scalarParityAut (parkerStandardParity e).toAdd (x i) •
        parkerCoordinateAction e (coordinateVector i) := by
  conv_lhs => rw [← coordinates_sum_basis x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact map_smulₛₗ (parkerCoordinateAction e) (x i) (coordinateVector i)

theorem parkerCoordinateAction_product (e : ParkerStandardGroup) (x y : Coordinates) :
    parkerCoordinateAction e (product x y) =
      product (parkerCoordinateAction e x) (parkerCoordinateAction e y) := by
  conv_rhs => rw [parkerCoordinateAction_sum_basis e x, parkerCoordinateAction_sum_basis e y]
  rw [product_sum_left]
  simp_rw [product_sum_right, product_smul_left, product_smul_right]
  conv_lhs => unfold product
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hstar (z : Scalar) : (scalarParityAut (parkerStandardParity e).toAdd).toRingHom (star z) =
      star (scalarParityAut (parkerStandardParity e).toAdd z) := scalarParityAut_star _ _
  rw [map_smulₛₗ, map_mul, hstar, hstar,
    ← product_coordinateVector, parkerCoordinateAction_basisProduct, smul_smul]

end Atlas.Fischer
