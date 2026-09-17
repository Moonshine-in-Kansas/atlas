import Atlas.LinearGroups.Symplectic.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F K : Type*} [Field F] [Field K]

/-- Transport of the actual full matrix group by a field isomorphism. -/
def fieldEquivSp (e : F ≃+* K) : Sp n F ≃* Sp n K where
  toFun g := ⟨g.val.map e,SymplecticGroup.map_mem g.prop e⟩
  invFun g := ⟨g.val.map e.symm,SymplecticGroup.map_mem g.prop e.symm⟩
  left_inv g := by apply Subtype.ext; ext i j; exact e.symm_apply_apply _
  right_inv g := by apply Subtype.ext; ext i j; exact e.apply_symm_apply _
  map_mul' g h := by apply Subtype.ext; exact Matrix.map_mul

def fieldEquivPSp (e : F ≃+* K) : PSp n F ≃* PSp n K :=
  QuotientGroup.congr _ _ (fieldEquivSp e) (Subgroup.map_center_eq (fieldEquivSp e))

@[simp] theorem fieldEquivPSp_projection (e : F ≃+* K) (g : Sp n F) :
    fieldEquivPSp e (projection g)=projection (fieldEquivSp e g) := rfl

end Atlas.Symplectic
