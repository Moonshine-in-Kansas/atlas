import Atlas.LinearGroups.Symplectic.Isometry
import Atlas.LinearGroups.Symplectic.Transvection

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]

/-- The full form-preserving subgroup of linear equivalences, with composition. -/
def linearIsometries : Subgroup (Vector n F ≃ₗ[F] Vector n F) where
  carrier := {g | ∀ x y,form (g x) (g y)=form x y}
  one_mem' := by intro x y; rfl
  mul_mem' := by intro g h hg hh x y; exact (hg (h x) (h y)).trans (hh x y)
  inv_mem' := by
    intro g hg x y
    have h := hg (g.symm x) (g.symm y)
    simpa using h.symm

/-- The full abstract isometry group and the primary matrix group agree multiplicatively. -/
def fullLinearIsometryEquiv : Sp n F ≃* linearIsometries (n := n) (F := F) where
  toFun g := ⟨toLinear g,preserves g⟩
  invFun g := ofLinear g.val g.prop
  left_inv g := by
    apply ext_action
    intro x
    exact ofLinear_apply (toLinear g) (preserves g) x
  right_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact ofLinear_apply g.val g.prop x
  map_mul' g h := by
    apply Subtype.ext
    exact toLinear.map_mul g h

@[simp] theorem fullLinearIsometryEquiv_action (g : Sp n F) (x : Vector n F) :
    (fullLinearIsometryEquiv g).val x = g • x := rfl

end Atlas.Symplectic
