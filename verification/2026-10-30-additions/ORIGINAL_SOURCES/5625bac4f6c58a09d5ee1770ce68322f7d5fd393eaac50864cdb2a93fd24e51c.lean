import F4Work.F4GeckOpposition
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! The faithful, reindexed action of the literal Chevalley F4 model. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.F4
open scoped Matrix
variable (R : Type*) [CommRing R]

def geckLinearEquiv (g : Model .F4 R) : (Fin 52 → R) ≃ₗ[R] (Fin 52 → R) where
  toLinearMap := Matrix.mulVecLin (chevalleyMatrixHom (R:=R) g)
  invFun := (chevalleyMatrixHom (R:=R) g⁻¹).mulVec
  left_inv v := by
    change chevalleyMatrixHom (R:=R) g⁻¹ *ᵥ (chevalleyMatrixHom (R:=R) g *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
  right_inv v := by
    change chevalleyMatrixHom (R:=R) g *ᵥ (chevalleyMatrixHom (R:=R) g⁻¹ *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]

def geckRepresentation : Model .F4 R →* ((Fin 52 → R) ≃ₗ[R] (Fin 52 → R)) where
  toFun := geckLinearEquiv R
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change chevalleyMatrixHom (R:=R) 1 *ᵥ v = v
    rw [map_one, Matrix.one_mulVec]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    change chevalleyMatrixHom (R:=R) (g*h) *ᵥ v = chevalleyMatrixHom (R:=R) g *ᵥ (chevalleyMatrixHom (R:=R) h *ᵥ v)
    rw [map_mul, Matrix.mulVec_mulVec]

theorem geckRepresentation_apply (g : Model .F4 R) (v : Fin 52 → R) :
    geckRepresentation R g v = chevalleyMatrixHom (R:=R) g *ᵥ v := rfl

theorem geckRepresentation_injective : Function.Injective (geckRepresentation R) := by
  intro g h he
  apply chevalleyMatrixHom_injective (R:=R)
  apply Matrix.ext_of_mulVec_single
  intro i
  exact congrArg (fun f : (Fin 52 → R) ≃ₗ[R] (Fin 52 → R) => f (Pi.single i 1)) he

end Atlas.Chevalley.Comparison.F4
