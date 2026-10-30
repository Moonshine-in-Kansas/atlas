import Atlas.LinearGroups.Chevalley.Comparison.G2.ActualGeckMatrices
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! The faithful, reindexed action of the literal Chevalley G2 model. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.G2
open scoped Matrix
variable (R : Type*) [CommRing R]

def geckLinearEquiv (g : Model .G2 R) : (Fin 14 → R) ≃ₗ[R] (Fin 14 → R) where
  toLinearMap := Matrix.mulVecLin (matrixHom R g)
  invFun := (matrixHom R g⁻¹).mulVec
  left_inv v := by
    change matrixHom R g⁻¹ *ᵥ (matrixHom R g *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
  right_inv v := by
    change matrixHom R g *ᵥ (matrixHom R g⁻¹ *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]

def geckRepresentation : Model .G2 R →* ((Fin 14 → R) ≃ₗ[R] (Fin 14 → R)) where
  toFun := geckLinearEquiv R
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change matrixHom R 1 *ᵥ v = v
    rw [map_one, Matrix.one_mulVec]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    change matrixHom R (g*h) *ᵥ v = matrixHom R g *ᵥ (matrixHom R h *ᵥ v)
    rw [map_mul, Matrix.mulVec_mulVec]

theorem geckRepresentation_apply (g : Model .G2 R) (v : Fin 14 → R) :
    geckRepresentation R g v = matrixHom R g *ᵥ v := rfl

theorem geckRepresentation_injective : Function.Injective (geckRepresentation R) := by
  intro g h he
  apply matrixHom_injective R
  apply Matrix.ext_of_mulVec_single
  intro i
  exact congrArg (fun f : (Fin 14 → R) ≃ₗ[R] (Fin 14 → R) => f (Pi.single i 1)) he

end Atlas.Chevalley.Comparison.G2
