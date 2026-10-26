import Atlas.LinearGroups.ReeF4.OppositeWedgeRelations
import Atlas.LinearGroups.ReeF4.MarkedBasis
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! An explicit section of the polar/cross map on the exterior square. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def diagonalWedge : ⋀[F]^2 (TraceZero F) := wedge (diagonalVector 0) (diagonalVector 1)

@[simp] theorem exteriorPolar_diagonalWedge : exteriorPolar (diagonalWedge (F:=F)) = 1 := by
  simp [diagonalWedge, diagonalPolar]

@[simp] theorem exteriorCross_diagonalWedge : exteriorCross (diagonalWedge (F:=F)) = 0 := by
  simp [diagonalWedge, diagonalCross]

def auxiliaryDiagonal (r : ShortRootLabel) : Fin 3 := if r.1=0 then 1 else 0

theorem auxiliaryDiagonal_ne (r : ShortRootLabel) : auxiliaryDiagonal r ≠ r.1 := by
  by_cases h : r.1=0
  · simp [auxiliaryDiagonal, h]
  · simp [auxiliaryDiagonal, h, Ne.symm h]

def exteriorLiftMarked : TraceZeroCoordinate → ⋀[F]^2 (TraceZero F)
  | .inl i => oppositeWedge (Fin.castLE (by decide) i,0) + diagonalWedge
  | .inr r => wedge (diagonalVector (auxiliaryDiagonal r)) (rootVector r)

theorem exteriorPolar_liftMarked (i : TraceZeroCoordinate) :
    exteriorPolar (exteriorLiftMarked (F:=F) i) = 0 := by
  cases i <;> simp [exteriorLiftMarked, oppositeWedge, rootPolar,
    diagonalRootPolar, CharTwo.add_self_eq_zero]

theorem exteriorCross_liftMarked (i : TraceZeroCoordinate) :
    exteriorCross (exteriorLiftMarked (F:=F) i) = markedBasis i := by
  cases i with
  | inl i =>
    simp only [exteriorLiftMarked, _root_.map_add, exteriorCross_diagonalWedge, add_zero,
      oppositeWedge, exteriorCross_wedge, markedBasis_diagonal]
    exact rootCross_opposite (Fin.castLE (by decide) i, 0)
  | inr r =>
    simp [exteriorLiftMarked, diagonalRootCross, auxiliaryDiagonal_ne, markedBasis_root]

def exteriorLift : TraceZero F →ₗ[F] ⋀[F]^2 (TraceZero F) :=
  markedBasis.constr F exteriorLiftMarked

theorem exteriorPolar_comp_lift :
    (exteriorPolar (F:=F)).comp exteriorLift = 0 := by
  apply markedBasis.ext
  intro i
  simp [exteriorLift, Module.Basis.constr_basis, exteriorPolar_liftMarked]

theorem exteriorCross_comp_lift :
    (exteriorCross (F:=F)).comp exteriorLift = LinearMap.id := by
  apply markedBasis.ext
  intro i
  simp [exteriorLift, Module.Basis.constr_basis, exteriorCross_liftMarked]

def exteriorJoint : (⋀[F]^2 (TraceZero F)) →ₗ[F] F × TraceZero F :=
  exteriorPolar.prod exteriorCross

def exteriorJointSection : F × TraceZero F →ₗ[F] ⋀[F]^2 (TraceZero F) where
  toFun p := p.1 • diagonalWedge + exteriorLift p.2
  map_add' p q := by simp [add_smul]; abel
  map_smul' a p := by simp [smul_add, smul_smul]

theorem exteriorJoint_section (p : F × TraceZero F) :
    exteriorJoint (exteriorJointSection p) = p := by
  have hp := LinearMap.congr_fun (exteriorPolar_comp_lift (F:=F)) p.2
  have hc := LinearMap.congr_fun (exteriorCross_comp_lift (F:=F)) p.2
  apply Prod.ext
  · simpa [exteriorJoint, exteriorJointSection] using hp
  · simpa [exteriorJoint, exteriorJointSection] using hc

theorem exteriorJoint_surjective : Function.Surjective (exteriorJoint (F:=F)) :=
  fun p => ⟨exteriorJointSection p, exteriorJoint_section p⟩

theorem starCarrier_eq_joint_ker : StarCarrier (F:=F) = exteriorJoint.ker := by
  ext x
  simp [StarCarrier, exteriorJoint, LinearMap.mem_ker, Prod.ext_iff]

end Atlas.ReeF4
