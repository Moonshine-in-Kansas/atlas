import Atlas.Fischer.BasicRootMaps
import Atlas.Fischer.ParkerCoordinateAction
import Atlas.Fischer.ParkerStandardOrder
import Atlas.Fischer.CocodeCoordinates

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Fischer
open Atlas.Codes

noncomputable def rootMapSemilinear (r : Coordinates) :
    Coordinates →ₛₗ[starRingEnd Scalar] Coordinates where
  toFun x := rootMap r x
  map_add' x y := rootMap_add r x y
  map_smul' a x := rootMap_smul r x a

noncomputable def coordinateCocodeMap (i : Omega) :
    Coordinates →ₛₗ[starRingEnd Scalar] Coordinates where
  toFun x := parkerCoordinateAction (parkerCocodeStandard (coordinateCocode i)) x
  map_add' x y := map_add _ _ _
  map_smul' a x := by
    have hb : (parkerStandardParity (parkerCocodeStandard (coordinateCocode i))).toAdd = 1 := by
      rw [parkerStandardParity_cocode, coordinateCocode_parity]
      rfl
    have h := (parkerCoordinateAction (parkerCocodeStandard (coordinateCocode i))).map_smulₛₗ a x
    simpa only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hb, scalarParityAut_one,
      starRingEnd_apply] using h

theorem coordinateCocodeMap_u (i j : Omega) : coordinateCocodeMap i (u j) = u j := by
  change parkerCoordinateAction (parkerCocodeStandard (coordinateCocode i)) (u j) = _
  rw [parkerCoordinateAction_u, parkerCocodeStandard_projection]
  rfl

theorem coordinateCocodeMap_xOctad (i : Omega) (O : Octad) :
    coordinateCocodeMap i (xOctad O) = if i ∈ O.val then -xOctad O else xOctad O := by
  classical
  change parkerCoordinateAction (parkerCocodeStandard (coordinateCocode i)) (xOctad O) = _
  rw [parkerCoordinateAction_xOctad]
  have hs : signedOctadSupport
      (parkerSignedOctadAction (parkerCocodeStandard (coordinateCocode i))
        (canonicalOctadLift O)) = O := by
    apply Subtype.ext
    exact octadWord_support O
  rw [signedOctadVector, hs]
  change parkerScalarSign (0 + cocodePairing (octadWord O) (coordinateCocode i)) • xOctad O = _
  rw [zero_add, cocodePairing_coordinate]
  have hb : ((octadWord O : BinaryWord) i = 0) ↔ i ∉ O.val := by
    rw [← octadWord_support O]
    simp [support]
  by_cases hi : i ∈ O.val <;> simp [parkerScalarSign, hb, hi]

theorem coordinateSemilinear_ext
    (f g : Coordinates →ₛₗ[starRingEnd Scalar] Coordinates)
    (h : ∀ k, f (coordinateVector k) = g (coordinateVector k)) : f = g := by
  classical
  apply (Pi.basisFun Scalar CoordinateIndex).ext
  intro k
  simpa only [Pi.basisFun_apply, coordinateVector] using h k

/-- The source identity τ_(r_i)=T_({i}+C), for the actual faithful standard action. -/
theorem rootMap_basicAxis_eq_cocode (i : Omega) (x : Coordinates) :
    rootMap (basicAxis i) x =
      parkerCoordinateAction (parkerCocodeStandard (coordinateCocode i)) x := by
  classical
  have hb (k : CoordinateIndex) : rootMap (basicAxis i) (coordinateVector k) =
      coordinateCocodeMap i (coordinateVector k) := by
    cases k with
    | inl j => simpa only [u] using (rootMap_basicAxis_u i j).trans (coordinateCocodeMap_u i j).symm
    | inr O => simpa only [xOctad] using (rootMap_basicAxis_xOctad i O).trans (coordinateCocodeMap_xOctad i O).symm
  have he : rootMapSemilinear (basicAxis i) = coordinateCocodeMap i := by
    apply coordinateSemilinear_ext
    exact hb
  exact congrArg (fun f : Coordinates →ₛₗ[starRingEnd Scalar] Coordinates => f x) he

theorem basicAxis_rootMap_antiunitary (i : Omega) : RootMapAntiunitary (basicAxis i) := by
  intro x y
  rw [rootMap_basicAxis_eq_cocode, rootMap_basicAxis_eq_cocode,
    parkerCoordinateAction_hermitian, parkerStandardParity_cocode, coordinateCocode_parity]
  exact scalarParityAut_one _

end Atlas.Fischer
