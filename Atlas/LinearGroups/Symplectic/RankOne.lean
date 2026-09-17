import Atlas.LinearGroups.Symplectic.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.GroupTheory.QuotientGroup.Basic

noncomputable section
namespace Atlas.Symplectic
open Matrix
variable {F : Type*} [Field F]

/-- The retained left/right marking in rank one becomes the two standard coordinates. -/
def rankOneIndex : Index 1 ≃ Fin 2 where
  toFun := Sum.elim (fun _ => 0) (fun _ => 1)
  invFun i := if i=0 then Sum.inl 0 else Sum.inr 0
  left_inv i := by rcases i with i|i <;> fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem rankOne_form_mul (M : Matrix (Index 1) (Index 1) F) (x y : Vector 1 F) :
    form (M *ᵥ x) (M *ᵥ y) = M.det * form x y := by
  rw [← Matrix.det_reindex_self rankOneIndex M,Matrix.det_fin_two]
  simp only [Matrix.reindex_apply]
  simp [rankOneIndex,form_apply,Matrix.mulVec,dotProduct,Fintype.sum_sum_type]
  ring

theorem rankOne_mem_iff_det (M : Matrix (Index 1) (Index 1) F) :
    M ∈ Matrix.symplecticGroup (Fin 1) F ↔ M.det=1 := by
  constructor
  · exact SymplecticGroup.det_eq_one
  · intro h
    apply mem_iff_preserves.mpr
    intro x y
    rw [rankOne_form_mul,h,one_mul]

def rankOneSL : Sp 1 F ≃* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun g := ⟨Matrix.reindexAlgEquiv F F rankOneIndex g.val,by
    rw [Matrix.det_reindexAlgEquiv]; exact determinant_one g⟩
  invFun g := ⟨Matrix.reindexAlgEquiv F F rankOneIndex.symm g.val,by
    apply (rankOne_mem_iff_det _).mpr
    rw [Matrix.det_reindexAlgEquiv]; exact g.prop⟩
  left_inv g := by
    apply Subtype.ext
    exact (Matrix.reindexAlgEquiv F F rankOneIndex).symm_apply_apply g.val
  right_inv g := by
    apply Subtype.ext
    exact (Matrix.reindexAlgEquiv F F rankOneIndex).apply_symm_apply g.val
  map_mul' g h := by
    apply Subtype.ext
    exact (Matrix.reindexAlgEquiv F F rankOneIndex).map_mul g.val h.val

def rankOnePSL : PSp 1 F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
  QuotientGroup.congr _ _ rankOneSL (Subgroup.map_center_eq rankOneSL)

@[simp] theorem rankOnePSL_projection (g : Sp 1 F) :
    rankOnePSL (projection g) = QuotientGroup.mk (rankOneSL g) := rfl

def rankOneVector : Vector 1 F ≃ₗ[F] (Fin 2 → F) :=
  LinearEquiv.funCongrLeft F F rankOneIndex.symm

theorem rankOneSL_action (g : Sp 1 F) (v : Vector 1 F) :
    rankOneVector (g • v) = rankOneSL g • rankOneVector v := by
  change rankOneVector (g.val *ᵥ v) =
    (Matrix.reindexAlgEquiv F F rankOneIndex g.val) *ᵥ rankOneVector v
  funext i
  fin_cases i <;>
    simp [rankOneVector,LinearEquiv.funCongrLeft,rankOneSL,Matrix.reindexAlgEquiv,
      Matrix.reindexRingEquiv,Matrix.reindex_apply,rankOneIndex,Matrix.mulVec,dotProduct,
      Fintype.sum_sum_type,Fin.sum_univ_two]

end Atlas.Symplectic

