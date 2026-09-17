import Atlas.LinearGroups.Orthogonal.B2ExteriorAction
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! # Actual exterior-square construction SL₄ → O⁺₆ in every characteristic -/
noncomputable section
namespace Atlas.Orthogonal.D3Exterior
open B2Exterior Matrix
variable {F : Type*} [CommRing F]

/-- Actual split-D coordinates on the six bivector minors, with the Pfaffian sign. -/
def coordinates : Six F ≃ₗ[F] VectorD 3 F where
  toFun w := Sum.elim ![w 0,w 1,w 2] ![w 5,-w 4,w 3]
  invFun v := ![v (.inl 0),v (.inl 1),v (.inl 2),v (.inr 2),-v (.inr 1),v (.inr 0)]
  left_inv w := by ext i; fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail]
  right_inv v := by ext i; rcases i with i|i <;> fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail]
  map_add' u v := by ext i; rcases i with i|i <;> fin_cases i <;> simp [add_comm]
  map_smul' c v := by ext i; rcases i with i|i <;> fin_cases i <;> simp

theorem coordinates_form (w : Six F) : formD 3 F (coordinates w) = pfaffian w := by
  simp [coordinates, Fin.sum_univ_succ, pfaffian_apply]
  ring

/-- The genuine exterior-square linear equivalence, with inverse induced by g⁻¹. -/
def exteriorAction (g : Matrix.SpecialLinearGroup (Fin 4) F) : Six F ≃ₗ[F] Six F where
  __ := exteriorMap g.val
  invFun := exteriorMap g⁻¹.val
  left_inv w := by
    change ((exteriorMap g⁻¹.val).comp (exteriorMap g.val)) w = w
    rw [← exteriorMap_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, exteriorMap_one, LinearMap.id_apply]
  right_inv w := by
    change ((exteriorMap g.val).comp (exteriorMap g⁻¹.val)) w = w
    rw [← exteriorMap_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, exteriorMap_one, LinearMap.id_apply]

def onD (g : Matrix.SpecialLinearGroup (Fin 4) F) : VectorD 3 F ≃ₗ[F] VectorD 3 F :=
  coordinates.symm.trans ((exteriorAction g).trans coordinates)

theorem onD_form (g : Matrix.SpecialLinearGroup (Fin 4) F) (v : VectorD 3 F) :
    formD 3 F (onD g v) = formD 3 F v := by
  change formD 3 F (coordinates (exteriorMap g.val (coordinates.symm v))) = _
  rw [coordinates_form, pfaffian_exteriorMap, g.det_coe, one_mul]
  simpa using (coordinates_form (coordinates.symm v)).symm

/-- Exterior square gives an actual homomorphism to the established split quadratic model. -/
def toOrthogonal : Matrix.SpecialLinearGroup (Fin 4) F →* O_DPlus 3 F where
  toFun g := ⟨onD g,onD_form g⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change coordinates (exteriorMap (1 : Matrix (Fin 4) (Fin 4) F) (coordinates.symm v)) = v
    rw [exteriorMap_one, LinearMap.id_apply, LinearEquiv.apply_symm_apply]
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change coordinates (exteriorMap (g*h).val (coordinates.symm v)) =
      coordinates (exteriorMap g.val (coordinates.symm (coordinates (exteriorMap h.val (coordinates.symm v)))))
    rw [LinearEquiv.symm_apply_apply, Matrix.SpecialLinearGroup.coe_mul,
      exteriorMap_mul, LinearMap.comp_apply]

end Atlas.Orthogonal.D3Exterior
