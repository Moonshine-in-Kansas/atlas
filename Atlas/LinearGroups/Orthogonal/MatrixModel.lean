import Atlas.LinearGroups.Orthogonal.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Faithful matrix adapters for the same quadratic isometry groups -/
noncomputable section
namespace Atlas.Orthogonal
open Matrix
variable {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
  [Fintype ι] [DecidableEq ι]
variable (Q : QuadraticForm F V) (b : Module.Basis ι F V)

def matrixLinearEquiv : Matrix.GeneralLinearGroup ι F ≃* (V ≃ₗ[F] V) :=
  (Matrix.GeneralLinearGroup.toLin' b).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F V)

def matrixIsometrySubgroup : Subgroup (Matrix.GeneralLinearGroup ι F) :=
  (isometrySubgroup Q).comap (matrixLinearEquiv b).toMonoidHom

theorem mem_matrixIsometry (g : Matrix.GeneralLinearGroup ι F) :
    g ∈ matrixIsometrySubgroup Q b ↔ ∀ x, Q (matrixLinearEquiv b g x) = Q x := Iff.rfl

/-- The matrix group is the full quadratic isometry carrier in the given basis. -/
def matrixIsometryEquiv : isometrySubgroup Q ≃* matrixIsometrySubgroup Q b where
  toFun g := ⟨(matrixLinearEquiv b).symm g.val, by
    change (matrixLinearEquiv b) ((matrixLinearEquiv b).symm g.val) ∈ isometrySubgroup Q
    rw [MulEquiv.apply_symm_apply]
    exact g.prop⟩
  invFun g := ⟨matrixLinearEquiv b g.val, g.prop⟩
  left_inv g := Subtype.ext ((matrixLinearEquiv b).apply_symm_apply g.val)
  right_inv g := Subtype.ext ((matrixLinearEquiv b).symm_apply_apply g.val)
  map_mul' g h := Subtype.ext ((matrixLinearEquiv b).symm.map_mul g.val h.val)

/-- Its faithful matrices act on the actual chosen coordinates. -/
theorem matrixLinearEquiv_coordinates (g : Matrix.GeneralLinearGroup ι F) (x : V) :
    b.equivFun (matrixLinearEquiv b g x) = g.val *ᵥ b.equivFun x := by
  change b.equivFun ((Matrix.GeneralLinearGroup.toLin' b g).toLinearEquiv x) = _
  rw [Matrix.GeneralLinearGroup.toLin'_apply]
  rw [Fintype.linearCombination_apply, ← b.equivFun_symm_apply]
  change b.equivFun (b.equivFun.symm (g.val *ᵥ b.equivFun x)) = _
  exact b.equivFun.apply_symm_apply _

end Atlas.Orthogonal
