import Atlas.Algebra.Albert.DirectionalCubic
import Atlas.LinearAlgebra.PolynomialSubstitution
import Mathlib.GroupTheory.GroupAction.Defs

/-! The full intrinsic unit-and-cubic stabilizer. -/
noncomputable section
namespace Atlas.Albert
open Matrix
variable {F : Type*} [CommRing F]

def coordinateAut : (Carrier F ≃ₗ[F] Carrier F) →*
    ((Coordinate → F) ≃ₗ[F] (Coordinate → F)) where
  toFun g := (coordinateEquiv.symm.trans g).trans coordinateEquiv
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

def matrixRepresentation : (Carrier F ≃ₗ[F] Carrier F) →*
    GeneralLinearGroup Coordinate F :=
  ((GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Coordinate → F))).symm.toMonoidHom).comp
    coordinateAut

theorem matrixRepresentation_apply (g : Carrier F ≃ₗ[F] Carrier F) (x : Carrier F) :
    (matrixRepresentation g).val *ᵥ coordinateEquiv x = coordinateEquiv (g x) := by
  change LinearMap.toMatrix' (coordinateAut g).toLinearMap *ᵥ coordinateEquiv x = _
  rw [LinearMap.toMatrix'_mulVec]
  simp [coordinateAut]

def polynomialStabilizer : Subgroup (Carrier F ≃ₗ[F] Carrier F) :=
  (Atlas.PolynomialLinear.stabilizer (normPolynomial (F := F))).comap matrixRepresentation ⊓
    MulAction.stabilizer (Carrier F ≃ₗ[F] Carrier F) (unit : Carrier F)

theorem mem_polynomialStabilizer (g : Carrier F ≃ₗ[F] Carrier F) :
    g ∈ polynomialStabilizer ↔
      Atlas.PolynomialLinear.substitute (matrixRepresentation g).val normPolynomial =
        normPolynomial ∧ g unit = unit := Iff.rfl

theorem stabilizer_norm (g : polynomialStabilizer (F := F)) (x : Carrier F) :
    norm (g.val x) = norm x := by
  have h := congrArg (MvPolynomial.eval (coordinateEquiv x)) g.property.1
  rw [Atlas.PolynomialLinear.eval_substitute, matrixRepresentation_apply,
    eval_normPolynomial, eval_normPolynomial] at h
  exact h

theorem stabilizer_unit (g : polynomialStabilizer (F := F)) : g.val unit = unit :=
  g.property.2

end Atlas.Albert
