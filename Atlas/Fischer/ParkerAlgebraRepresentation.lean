import Atlas.Fischer.SemilinearAlgebraAutomorphisms
import Atlas.Fischer.ParkerMultiplicativity
import Atlas.Fischer.ParkerCoordinateFaithfulness
import Atlas.Fischer.ScalarAutomorphisms

namespace Atlas.Fischer
open Atlas.Codes

noncomputable def parkerAlgebraElement (e : ParkerStandardGroup) : SemilinearAlgebraAutomorphism :=
  ⟨(parkerCoordinateAction e).toEquiv,
    fun x y => map_add (parkerCoordinateAction e) x y,
    parkerCoordinateAction_product e,
    (parkerStandardParity e).toAdd,
    fun r x => map_smulₛₗ (parkerCoordinateAction e) r x⟩

noncomputable def parkerAlgebraRepresentation : ParkerStandardGroup →* SemilinearAlgebraAutomorphism where
  toFun := parkerAlgebraElement
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    exact parkerCoordinateAction_one
  map_mul' e f := by
    apply Subtype.ext
    apply Equiv.ext
    exact parkerCoordinateAction_mul e f

theorem parkerAlgebraRepresentation_injective : Function.Injective parkerAlgebraRepresentation := by
  intro e f h
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Coordinates)
  intro x
  exact congrArg (fun k : SemilinearAlgebraAutomorphism => k.val x) h

theorem parkerAlgebraRepresentation_parity (e : ParkerStandardGroup) :
    semilinearAlgebraParity (parkerAlgebraRepresentation e) = (parkerStandardParity e).toAdd := by
  apply semilinearAlgebraParity_unique
  intro r x
  exact map_smulₛₗ (parkerCoordinateAction e) r x

noncomputable def scalarAlgebraElement (a : Mu3) : SemilinearAlgebraAutomorphism :=
  ⟨(scalarPhaseEquiv a).toEquiv,
    fun x y => map_add (scalarPhaseEquiv a) x y,
    fun x y => (scalarPhaseEquiv_product a x y).symm,
    0, fun r x => by simpa using map_smul (scalarPhaseEquiv a) r x⟩

noncomputable def scalarAlgebraRepresentation : Mu3 →* SemilinearAlgebraAutomorphism where
  toFun := scalarAlgebraElement
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change (1 : Scalar) • x = x
    exact one_smul _ x
  map_mul' a b := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change ((a.val.val : Scalar) * b.val.val) • x = a.val.val • (b.val.val • x)
    exact mul_smul _ _ _

theorem scalarAlgebraRepresentation_injective : Function.Injective scalarAlgebraRepresentation := by
  intro a b h
  let i : CoordinateIndex := Sum.inl (Classical.arbitrary Omega)
  have hh := congrArg (fun e : SemilinearAlgebraAutomorphism => e.val (coordinateVector i)) h
  change (a.val.val : Scalar) • coordinateVector i = b.val.val • coordinateVector i at hh
  have he := (smul_left_injective Scalar (coordinateVector_ne_zero i)) hh
  apply Subtype.ext
  exact Units.ext he

theorem scalarAlgebraRepresentation_parity (a : Mu3) :
    semilinearAlgebraParity (scalarAlgebraRepresentation a) = 0 := by
  apply semilinearAlgebraParity_unique
  intro r x
  change scalarPhaseEquiv a (r • x) = scalarParityAut 0 r • scalarPhaseEquiv a x
  rw [scalarParityAut_zero]
  exact map_smul (scalarPhaseEquiv a) r x

end Atlas.Fischer
