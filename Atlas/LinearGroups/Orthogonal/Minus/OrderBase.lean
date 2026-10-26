import Atlas.LinearGroups.Orthogonal.Minus.Basic
import Atlas.LinearGroups.Orthogonal.Minus.PlaneIsometries
import Atlas.LinearGroups.Orthogonal.IsometryTransport

/-! The internal k=0 space is the actual anisotropic norm plane. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def zeroRankIsometry (hdeg : Module.finrank F K = 2) :
    (form hdeg 0).IsometryEquiv (normForm hdeg) where
  toFun x := x.2
  invFun x := (0,x)
  left_inv x := Prod.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_app' x := by simp [form_apply,formD_apply,normForm_apply]

def zeroRankGroupEquiv (hdeg : Module.finrank F K = 2) : O hdeg 0 ≃* PlaneO hdeg :=
  isometryGroupTransport (zeroRankIsometry hdeg)

theorem card_full_zero (hdeg : Module.finrank F K = 2) :
    Nat.card (O hdeg 0) = 2*(Nat.card F+1) := by
  rw [Nat.card_congr (zeroRankGroupEquiv hdeg).toEquiv,card_planeO]
end Atlas.Orthogonal.Minus
