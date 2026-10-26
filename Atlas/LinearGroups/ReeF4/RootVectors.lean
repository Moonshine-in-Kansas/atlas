import Atlas.LinearGroups.ReeF4.HurwitzRoots
import Atlas.Algebra.Albert.TraceZeroBaseChange
import Mathlib.Data.ZMod.Basic

/-! Marked root vectors in the actual Albert trace kernel. -/
namespace Atlas.ReeF4
open Atlas.Albert
variable {F R : Type*} [CommRing F] [CommRing R]

def rootVector (r : ShortRootLabel) : TraceZero F :=
  ⟨(0, Pi.single r.1 (Pi.single r.2 1)), by simp [traceLinear, trace]⟩

theorem rootVector_map (f : F →+* R) (r : ShortRootLabel) :
    traceZeroMap f (rootVector r) = rootVector r := by
  apply Subtype.ext
  apply Prod.ext
  · funext i; simp [traceZeroMap, rootVector, map]
  · funext i j
    by_cases hi : i = r.1 <;> simp [traceZeroMap, rootVector, map, Pi.single_apply, hi]

variable [CharP F 2] [CharP R 2]

def diagonalVector (i : Fin 3) : TraceZero F :=
  traceZeroProjection (Pi.single i 1, 0)

theorem diagonalVector_map (f : F →+* R) (i : Fin 3) :
    traceZeroMap f (diagonalVector i) = diagonalVector i := by
  rw [diagonalVector, ← traceZeroProjection_map]
  congr 1
  apply Prod.ext
  · funext j; simp [map, Pi.single_apply]
  · funext j k; simp [map]

theorem diagonalVector_sum : diagonalVector (F:=F) 0 + diagonalVector 1 + diagonalVector 2 = 0 := by
  unfold diagonalVector
  rw [← _root_.map_add, ← _root_.map_add]
  have h : ((Pi.single 0 1, 0) : Carrier F) + (Pi.single 1 1, 0) +
      (Pi.single 2 1, 0) = unit := by
    apply Prod.ext
    · funext i; fin_cases i <;> simp [Pi.single_apply, unit]
    · funext i j; simp [unit]
  rw [h, traceZeroProjection_unit]

end Atlas.ReeF4
