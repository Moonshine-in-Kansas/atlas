import Atlas.Fischer.ParkerOctadProductAction
import Atlas.Fischer.SignedMonomialGeometry

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Fischer
open Atlas.Codes

/-- The manuscript action in left-action convention: source coordinate signs
are transported by the actual marked permutation, with parity conjugation. -/
noncomputable def parkerCoordinateAction (e : ParkerStandardGroup) :
    Coordinates ≃ₛₗ[(scalarParityAut (parkerStandardParity e).toAdd).toRingHom] Coordinates :=
  parkerSignedMonomial (parkerStandardParity e).toAdd (parkerCoordinateEquiv e)
    (parkerCoordinateSign e)

theorem parkerCoordinateAction_hermitian (e : ParkerStandardGroup) (x y : Coordinates) :
    hermitian (parkerCoordinateAction e x) (parkerCoordinateAction e y) =
      scalarParityAut (parkerStandardParity e).toAdd (hermitian x y) :=
  parkerSignedMonomial_hermitian _ _ _ _ (parkerCoordinateEquiv_weight e) x y

theorem parkerCoordinateAction_basis (e : ParkerStandardGroup) (i : CoordinateIndex) :
    parkerCoordinateAction e (coordinateVector i) =
      parkerScalarSign (parkerCoordinateSign e i) • coordinateVector (parkerCoordinateEquiv e i) := by
  classical
  funext k
  by_cases h : k = parkerCoordinateEquiv e i
  · subst k
    simp [parkerCoordinateAction, parkerSignedMonomial, coordinateVector, Pi.single_apply]
  · have hi : (parkerCoordinateEquiv e).symm k ≠ i := by
      intro hi
      apply h
      rw [← hi, Equiv.apply_symm_apply]
    simp [parkerCoordinateAction, parkerSignedMonomial, coordinateVector, Pi.single_apply,
      h, Ne.symm h, hi, Ne.symm hi]

theorem parkerCoordinateAction_u (e : ParkerStandardGroup) (i : Omega) :
    parkerCoordinateAction e (u i) = u ((parkerStandardProjection e).val i) := by
  rw [u, parkerCoordinateAction_basis]
  change parkerScalarSign 0 • u ((parkerStandardProjection e).val i) = _
  simp [parkerScalarSign]

theorem parkerSignedOctadSupport_canonical (O : Octad) :
    signedOctadSupport (canonicalOctadLift O) = O := by
  apply Subtype.ext
  exact octadWord_support O

theorem parkerCoordinateAction_xOctad (e : ParkerStandardGroup) (O : Octad) :
    parkerCoordinateAction e (xOctad O) =
      signedOctadVector (parkerSignedOctadAction e (canonicalOctadLift O)) := by
  rw [xOctad, parkerCoordinateAction_basis]
  unfold signedOctadVector
  rw [parkerSignedOctadAction_support, parkerSignedOctadSupport_canonical]
  rfl

theorem parkerCoordinateAction_signedOctad (e : ParkerStandardGroup) (d : SignedOctad) :
    parkerCoordinateAction e (signedOctadVector d) =
      signedOctadVector (parkerSignedOctadAction e d) := by
  have h := signedOctadAssignment_ext
    (fun q => parkerCoordinateAction e (signedOctadVector q))
    (fun q => signedOctadVector (parkerSignedOctadAction e q))
    (fun q => by rw [signedOctadVector_negate, map_neg])
    (fun q => by rw [parkerSignedOctadAction_negate, signedOctadVector_negate])
    (fun O => by rw [signedOctadVector_canonical]; exact parkerCoordinateAction_xOctad e O)
  exact congrFun h d

theorem parkerCoordinateAction_one (x : Coordinates) : parkerCoordinateAction 1 x = x := by
  have hp : parkerCoordinateEquiv 1 = 1 := Equiv.ext parkerCoordinateEquiv_one
  have hs : parkerCoordinateSign 1 = fun _ => 0 := funext parkerCoordinateSign_one
  unfold parkerCoordinateAction
  rw [map_one, hp, hs]
  exact parkerSignedMonomial_one x

theorem parkerCoordinateAction_mul (e f : ParkerStandardGroup) (x : Coordinates) :
    parkerCoordinateAction (e * f) x = parkerCoordinateAction e (parkerCoordinateAction f x) := by
  have hp : parkerCoordinateEquiv (e * f) = parkerCoordinateEquiv e * parkerCoordinateEquiv f :=
    Equiv.ext (parkerCoordinateEquiv_mul e f)
  have hs : parkerCoordinateSign (e * f) =
      fun i => parkerCoordinateSign e (parkerCoordinateEquiv f i) + parkerCoordinateSign f i :=
    funext (parkerCoordinateSign_mul e f)
  have hb : (parkerStandardParity (e * f)).toAdd =
      (parkerStandardParity e).toAdd + (parkerStandardParity f).toAdd :=
    congrArg Multiplicative.toAdd (map_mul parkerStandardParity e f)
  unfold parkerCoordinateAction
  rw [hp, hs, hb]
  exact parkerSignedMonomial_comp _ _ _ _ _ _ x

noncomputable instance : MulAction ParkerStandardGroup Coordinates where
  smul := fun e x => parkerCoordinateAction e x
  one_smul := parkerCoordinateAction_one
  mul_smul := parkerCoordinateAction_mul

end Atlas.Fischer
