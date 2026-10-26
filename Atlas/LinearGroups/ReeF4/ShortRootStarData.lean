import Atlas.LinearGroups.ReeF4.ShortRootCoordinates
import Atlas.LinearGroups.ReeF4.LongRootStarData

/-! Coordinate data for the short-root equivariance defect. In contrast to the
long-root operator, both the projected cross and the polar form occur. Their
common kernel is the actual exterior-square domain of the candidate star map. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F R : Type*} [CommRing F] [CharP F 2] [CommRing R] [CharP R 2]

def shortRootSupport : TraceZeroCoordinate → List TraceZeroCoordinate
  | .inl 0 => [.inl 0]
  | .inl _ => [.inl 1, .inr (0,3)]
  | .inr (0,3) => [.inr (0,3), .inr (0,2)]
  | .inr (0,4) => [.inr (0,4), .inl 0, .inr (0,3), .inr (0,2)]
  | .inr (0,5) => [.inr (0,5), .inr (0,4), .inl 0, .inr (0,2)]
  | .inr (1,0) => [.inr (1,0), .inr (2,0)]
  | .inr (1,1) => [.inr (1,1), .inr (1,0), .inr (2,0)]
  | .inr (1,3) => [.inr (1,3), .inr (2,4), .inr (1,2)]
  | .inr (1,5) => [.inr (1,5), .inr (2,5), .inr (1,4)]
  | .inr (1,6) => [.inr (1,6), .inr (2,6)]
  | .inr (1,7) => [.inr (1,7), .inr (1,6), .inr (2,6)]
  | .inr (2,1) => [.inr (2,1), .inr (1,1), .inr (2,0)]
  | .inr (2,2) => [.inr (2,2), .inr (1,2)]
  | .inr (2,3) => [.inr (2,3), .inr (1,4)]
  | .inr (2,4) => [.inr (2,4), .inr (2,2), .inr (1,2)]
  | .inr (2,5) => [.inr (2,5), .inr (2,3), .inr (1,4)]
  | .inr (2,7) => [.inr (2,7), .inr (1,7), .inr (2,6)]
  | .inr r => [.inr r]

theorem shortRootImage_support (i : TraceZeroCoordinate) :
    shortRootImage (F := F) i = ((shortRootSupport i).map starMarkedVector).sum := by
  rcases i with i | ⟨b,j⟩
  · fin_cases i <;> simp [shortRootImage, shortRootSupport, starMarkedVector, add_assoc]
  · fin_cases b <;> fin_cases j <;>
      simp [shortRootImage, shortRootSupport, starMarkedVector, add_assoc]

def shortRootStarCoefficient (i j : TraceZeroCoordinate) : TraceZero F :=
  ((shortRootSupport i).map (fun a =>
    ((shortRootSupport j).map (extensionCoefficient a)).sum)).sum

/-- The ten nonzero marked columns of the cross correction. The marked diagonal
coordinates are exchanged relative to the first two Albert diagonal entries. -/
def shortRootStarCorrection (w : TraceZero F) : TraceZero F :=
  w.val.1 1 • rootVector (0,3) + w.val.1 0 • rootVector (0,2) +
  w.val.2 0 0 • rootVector (1,0) + w.val.2 0 1 • rootVector (2,2) +
  w.val.2 0 2 • rootVector (0,2) + w.val.2 0 3 • rootVector (0,2) +
  w.val.2 0 4 • rootVector (0,2) +
  w.val.2 0 5 • (rootVector (0,2) + rootVector (0,4)) +
  w.val.2 0 6 • rootVector (2,3) + w.val.2 0 7 • rootVector (1,6)

def shortRootStarCorrectionLinear : TraceZero F →ₗ[F] TraceZero F where
  toFun := shortRootStarCorrection
  map_add' u v := by simp [shortRootStarCorrection, add_smul]; abel
  map_smul' a u := by simp [shortRootStarCorrection, smul_add, smul_smul, mul_comm]

def shortRootStarPolarCorrection (a : F) : TraceZero F := a • rootVector (0,3)

def shortRootStarPolarCorrectionLinear : F →ₗ[F] TraceZero F where
  toFun := shortRootStarPolarCorrection
  map_add' a b := by simp [shortRootStarPolarCorrection, add_smul]
  map_smul' a b := by simp [shortRootStarPolarCorrection, smul_smul, smul_eq_mul]

theorem shortRootStarCorrection_map (f : F →+* R) (w : TraceZero F) :
    traceZeroMap f (shortRootStarCorrection w) =
      shortRootStarCorrection (traceZeroMap f w) := by
  change traceZeroScalarMap f _ = _
  simp only [shortRootStarCorrection, _root_.map_add, LinearMap.map_smulₛₗ]
  simp only [traceZeroScalarMap_apply, rootVector_map]
  rfl

theorem shortRootStarPolarCorrection_map (f : F →+* R) (a : F) :
    traceZeroMap f (shortRootStarPolarCorrection a) = shortRootStarPolarCorrection (f a) := by
  change traceZeroScalarMap f _ = _
  simp only [shortRootStarPolarCorrection, LinearMap.map_smulₛₗ,
    traceZeroScalarMap_apply, rootVector_map]

end Atlas.ReeF4
