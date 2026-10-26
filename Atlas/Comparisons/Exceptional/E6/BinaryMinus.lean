import Atlas.Comparisons.Exceptional.E6.BinaryChart
import Atlas.LinearGroups.Orthogonal.Minus.Basic
import Atlas.LinearGroups.Orthogonal.IsometryTransport

/-! The binary E6 form is isometric to the existing norm-plane minus model.
Any marked linear basis of the binary quadratic extension gives the same norm
polynomial: both planes have precisely one zero. -/
noncomputable section
namespace Atlas.Comparisons.E6Lattice
open Atlas.Orthogonal
variable {K : Type*} [Field K] [Finite K] [Algebra (ZMod 2) K]
variable (hdeg : Module.finrank (ZMod 2) K = 2)

/-- A basis marking of the actual quadratic extension. -/
def binaryPlaneCoordinates : (Fin 2 → ZMod 2) ≃ₗ[ZMod 2] K :=
  LinearEquiv.ofFinrankEq _ _ (by simpa using hdeg.symm)

theorem binaryPlaneCoordinates_norm (a b : ZMod 2) :
    Minus.normForm hdeg (binaryPlaneCoordinates hdeg ![a,b]) = a^2+a*b+b^2 := by
  have hbin : ∀ x y : ZMod 2, (x = 0 ↔ y = 0) → x = y := by decide
  apply hbin
  rw [Minus.normForm_eq_zero_iff, (binaryPlaneCoordinates hdeg).map_eq_zero_iff,
    binary_anisotropic_plane]
  simp [funext_iff, Fin.forall_fin_succ]

/-- Coordinate grouping retains the two marked hyperbolic pairs. -/
def binaryMinusCoordinates : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] Minus.Vector 2 (ZMod 2) K where
  toFun x := (Sum.elim ![x 0,x 2] ![x 1,x 3], binaryPlaneCoordinates hdeg ![x 4,x 5])
  invFun v := ![v.1 (.inl 0),v.1 (.inr 0),v.1 (.inl 1),v.1 (.inr 1),
    ((binaryPlaneCoordinates hdeg).symm v.2) 0, ((binaryPlaneCoordinates hdeg).symm v.2) 1]
  left_inv x := by
    funext i
    fin_cases i <;> simp
  right_inv v := by
    apply Prod.ext
    · funext i
      rcases i with i | i <;> fin_cases i <;> rfl
    · change binaryPlaneCoordinates hdeg
        ![((binaryPlaneCoordinates hdeg).symm v.2) 0,
          ((binaryPlaneCoordinates hdeg).symm v.2) 1] = v.2
      have he : ![((binaryPlaneCoordinates hdeg).symm v.2) 0,
          ((binaryPlaneCoordinates hdeg).symm v.2) 1] =
          (binaryPlaneCoordinates hdeg).symm v.2 := by
        funext i; fin_cases i <;> rfl
      rw [he, LinearEquiv.apply_symm_apply]
  map_add' x y := by
    apply Prod.ext
    · funext i; rcases i with i | i <;> fin_cases i <;> rfl
    · change binaryPlaneCoordinates hdeg ![x 4+y 4,x 5+y 5] =
        binaryPlaneCoordinates hdeg ![x 4,x 5] + binaryPlaneCoordinates hdeg ![y 4,y 5]
      rw [← map_add]
      congr 1
      funext i; fin_cases i <;> rfl
  map_smul' a x := by
    apply Prod.ext
    · funext i; rcases i with i | i <;> fin_cases i <;> rfl
    · change binaryPlaneCoordinates hdeg ![a • x 4,a • x 5] =
        a • binaryPlaneCoordinates hdeg ![x 4,x 5]
      rw [← map_smul]
      congr 1
      funext i; fin_cases i <;> rfl

/-- Actual isometry onto the retained quadratic-extension norm model. -/
def binaryMinusWittIsometry : binaryWittForm.IsometryEquiv (Minus.form hdeg 2) where
  toLinearEquiv := binaryMinusCoordinates hdeg
  map_app' x := by
    change Minus.form hdeg 2 (binaryMinusCoordinates hdeg x) = binaryWittForm x
    rw [Minus.form_apply]
    change formD 2 (ZMod 2) (Sum.elim ![x 0,x 2] ![x 1,x 3]) +
      Minus.normForm hdeg (binaryPlaneCoordinates hdeg ![x 4,x 5]) = binaryWittForm x
    rw [binaryPlaneCoordinates_norm, binaryWittForm_apply]
    simp [formD_apply, Fin.sum_univ_succ]
    ring

/-- The concrete E6 reduction and the public minus space have equivalent full isometry groups. -/
def binaryMinusIsometry : (form (ZMod 2)).IsometryEquiv (Minus.form hdeg 2) :=
  binaryWittIsometry.symm.trans (binaryMinusWittIsometry hdeg)

def binaryMinusOrthogonalEquiv : isometrySubgroup (form (ZMod 2)) ≃* Minus.O hdeg 2 :=
  isometryGroupTransport (binaryMinusIsometry hdeg)

end Atlas.Comparisons.E6Lattice
