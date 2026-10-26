import Atlas.LinearGroups.ReeF4.MarkedBasis

/-! Wilson R1, §4, page 7: the short-root operator x on the marked Albert
trace kernel. Labels −4,−3,−2,−1,1,2,3,4 have indices 0,…,7; the
three blocks carry zero, one and two primes respectively. This file only
constructs the source linear operator, without asserting star preservation. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def shortRootImage : TraceZeroCoordinate → TraceZero F
  | .inl 0 => diagonalVector 0
  | .inl _ => diagonalVector 1 + rootVector (0,3)
  | .inr (0,3) => rootVector (0,3) + rootVector (0,2)
  | .inr (0,4) => rootVector (0,4) + diagonalVector 0 + rootVector (0,3) + rootVector (0,2)
  | .inr (0,5) => rootVector (0,5) + rootVector (0,4) + diagonalVector 0 + rootVector (0,2)
  | .inr (1,0) => rootVector (1,0) + rootVector (2,0)
  | .inr (1,1) => rootVector (1,1) + rootVector (1,0) + rootVector (2,0)
  | .inr (1,3) => rootVector (1,3) + rootVector (2,4) + rootVector (1,2)
  | .inr (1,5) => rootVector (1,5) + rootVector (2,5) + rootVector (1,4)
  | .inr (1,6) => rootVector (1,6) + rootVector (2,6)
  | .inr (1,7) => rootVector (1,7) + rootVector (1,6) + rootVector (2,6)
  | .inr (2,1) => rootVector (2,1) + rootVector (1,1) + rootVector (2,0)
  | .inr (2,2) => rootVector (2,2) + rootVector (1,2)
  | .inr (2,3) => rootVector (2,3) + rootVector (1,4)
  | .inr (2,4) => rootVector (2,4) + rootVector (2,2) + rootVector (1,2)
  | .inr (2,5) => rootVector (2,5) + rootVector (2,3) + rootVector (1,4)
  | .inr (2,7) => rootVector (2,7) + rootVector (1,7) + rootVector (2,6)
  | .inr r => rootVector r

def shortRootLinear : TraceZero F →ₗ[F] TraceZero F :=
  markedBasis.constr F shortRootImage

@[simp] theorem shortRootLinear_basis (i : TraceZeroCoordinate) :
    shortRootLinear (markedBasis (F := F) i) = shortRootImage i := by
  simp [shortRootLinear]

@[simp] theorem shortRootLinear_root (r : ShortRootLabel) :
    shortRootLinear (rootVector (F := F) r) = shortRootImage (.inr r) := by
  rw [← markedBasis_root]
  exact shortRootLinear_basis _

@[simp] theorem shortRootLinear_diagonal_zero :
    shortRootLinear (diagonalVector (F := F) 0) = diagonalVector 0 := by
  simpa [markedBasis_diagonal, shortRootImage] using shortRootLinear_basis (F := F) (.inl 0)

@[simp] theorem shortRootLinear_diagonal_one :
    shortRootLinear (diagonalVector (F := F) 1) = diagonalVector 1 + rootVector (0,3) := by
  simpa [markedBasis_diagonal, shortRootImage] using shortRootLinear_basis (F := F) (.inl 1)

end Atlas.ReeF4
