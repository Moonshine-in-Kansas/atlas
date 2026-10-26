import Atlas.Algebra.Albert.TraceZeroSemilinear
import Atlas.LinearGroups.ReeF4.LongRootScalar
import Atlas.LinearGroups.ReeF4.PartialCandidate

/-! Coordinate data for the defect of long-root equivariance. The defect will
factor through the actual projected cross product, hence vanish on its kernel. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F R : Type*} [CommRing F] [CharP F 2] [CommRing R] [CharP R 2]

def starMarkedVector : TraceZeroCoordinate → TraceZero F
  | .inl i => diagonalVector (Fin.castLE (by decide) i)
  | .inr r => rootVector r

theorem starMarkedVector_basis (i : TraceZeroCoordinate) :
    starMarkedVector (F := F) i = markedBasis i := by
  cases i <;> simp [starMarkedVector, markedBasis_diagonal, markedBasis_root]

theorem starMarkedVector_map (f : F →+* R) (i : TraceZeroCoordinate) :
    traceZeroMap f (starMarkedVector i) = starMarkedVector i := by
  cases i <;> simp [starMarkedVector, diagonalVector_map, rootVector_map]

def longRootSupport : TraceZeroCoordinate → List TraceZeroCoordinate
  | .inl 0 => [.inl 0, .inr (1,3)]
  | .inl _ => [.inl 1]
  | .inr (0,1) => [.inr (0,1), .inr (2,1)]
  | .inr (0,2) => [.inr (0,2), .inr (2,2), .inr (2,1), .inr (0,1)]
  | .inr (0,3) => [.inr (0,3), .inr (2,4)]
  | .inr (0,6) => [.inr (0,6), .inr (0,5)]
  | .inr (0,7) => [.inr (0,7), .inr (2,7)]
  | .inr (1,2) => [.inr (1,2), .inr (1,1)]
  | .inr (1,4) => [.inr (1,4), .inl 1, .inr (1,3)]
  | .inr (1,6) => [.inr (1,6), .inr (1,5)]
  | .inr (2,0) => [.inr (2,0), .inr (0,0)]
  | .inr (2,2) => [.inr (2,2), .inr (2,1)]
  | .inr (2,3) => [.inr (2,3), .inr (0,4)]
  | .inr (2,5) => [.inr (2,5), .inr (0,5)]
  | .inr (2,6) => [.inr (2,6), .inr (0,6), .inr (2,5), .inr (0,5)]
  | .inr r => [.inr r]

theorem longRootImage_support (i : TraceZeroCoordinate) :
    longRootImage (F := F) i = ((longRootSupport i).map starMarkedVector).sum := by
  rcases i with i | ⟨b,j⟩
  · fin_cases i <;> simp [longRootImage, longRootSupport, starMarkedVector, add_assoc]
  · fin_cases b <;> fin_cases j <;>
      simp [longRootImage, longRootSupport, starMarkedVector, add_assoc]

def longRootStarCoefficient (i j : TraceZeroCoordinate) : TraceZero F :=
  ((longRootSupport i).map (fun a =>
    ((longRootSupport j).map (extensionCoefficient a)).sum)).sum

/-- The six nonzero coordinate columns of the cross-product correction. -/
def longRootStarCorrection (w : TraceZero F) : TraceZero F :=
  w.val.2 1 0 • rootVector (1,1) + w.val.2 1 1 • rootVector (2,1) +
  w.val.2 1 2 • (rootVector (0,1) + rootVector (2,1)) +
  w.val.2 1 5 • rootVector (0,5) +
  w.val.2 1 6 • (rootVector (0,5) + rootVector (2,5)) +
  w.val.2 1 7 • rootVector (1,5)

def longRootStarCorrectionLinear : TraceZero F →ₗ[F] TraceZero F where
  toFun := longRootStarCorrection
  map_add' u v := by simp [longRootStarCorrection, add_smul]; abel
  map_smul' a u := by simp [longRootStarCorrection, smul_add, smul_smul, mul_comm]

theorem longRootStarCorrection_map (f : F →+* R) (w : TraceZero F) :
    traceZeroMap f (longRootStarCorrection w) =
      longRootStarCorrection (traceZeroMap f w) := by
  change traceZeroScalarMap f _ = _
  simp only [longRootStarCorrection, _root_.map_add, LinearMap.map_smulₛₗ]
  simp only [traceZeroScalarMap_apply, rootVector_map]
  rfl

end Atlas.ReeF4
