import Atlas.Tits.FusionGeneration
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace Atlas.Tits
open Atlas.Rudvalis Atlas.Codes.Quaternary
open scoped BigOperators

/-- The existing original real coordinates, used only for small operator identities. -/
noncomputable def originalMatrix : Module.End ℚ RationalSpace ≃+*
    Matrix SeedCoordinate SeedCoordinate ℚ :=
  seedTransportLinear.symm.conjRingEquiv.trans LinearMap.toMatrixAlgEquiv'.toRingEquiv

theorem originalMatrix_apply (f : Module.End ℚ RationalSpace) (i j : SeedCoordinate) :
    originalMatrix f i j = seedTransportLinear.symm
      (f (seedTransportLinear (Pi.single j 1))) i := rfl

noncomputable def originalGroupMatrix : gaussianLatticeGroup →*
    Matrix SeedCoordinate SeedCoordinate ℚ where
  toFun g := originalMatrix g.val.toLinearMap
  map_one' := originalMatrix.map_one
  map_mul' g h := originalMatrix.map_mul g.val.toLinearMap h.val.toLinearMap

theorem originalGroupMatrix_injective : Function.Injective originalGroupMatrix := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact originalMatrix.injective he

theorem originalMatrix_frame : originalGroupMatrix gaussianFrameExchange =
    (1/4:ℚ) • (fun i j => (frameComparisonRaw j i : ℚ)) := by
  ext i j
  change originalMatrix gaussianFrameExchange.val.toLinearMap i j = _
  rw [gaussianFrameExchange_val,originalMatrix_apply]
  change seedTransportLinear.symm (frameComparison (seedTransportLinear (Pi.single j 1))) i = _
  rw [frameComparison_raw_formula]
  simp [LinearEquiv.symm_apply_apply,Pi.single_apply,Matrix.smul_apply,smul_eq_mul,ite_mul]
  ring_nf
  rw [← Finset.sum_mul]
  simp

theorem originalMatrix_monomial (g : codeGroup) (a : SignedCoordinates SeedCoordinate)
    (ha : g.val = seedConjugateHom a) :
    originalGroupMatrix (codeGaussianHom g) =
      fun i j => ((liftedCoordinateHom a (Pi.single j 1 : SeedCoordinate → ℤ) i : ℤ) : ℚ) := by
  ext i j
  rw [show originalGroupMatrix (codeGaussianHom g) i j =
    originalMatrix (rationalMonomialHom g.val).toLinearMap i j from rfl,originalMatrix_apply,ha]
  change seedTransportLinear.symm
    (liftedCoordinateHom (seedConjugateMonomial a) (seedTransportLinear (Pi.single j 1))) i = _
  rw [seedConjugate_lifted_transport,LinearEquiv.symm_apply_apply]
  simp [liftedCoordinateHom,liftedCoordinateAction,liftedSign,Pi.single_apply]

end Atlas.Tits
