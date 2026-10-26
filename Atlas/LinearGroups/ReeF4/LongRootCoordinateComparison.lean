import Atlas.LinearGroups.ReeF4.LongRootCoordinates
import Atlas.Algebra.Albert.TraceZeroScalarForms

/-! Check the 26 binary basis images in the kernel, and transport this linear
identity to arbitrary characteristic-two coefficient rings. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F R : Type*} [CommRing F] [CommRing R] [CharP F 2] [CharP R 2]

theorem longRootFormula_map (f : F →+* R) (w : Carrier F) :
    longRootFormula (Albert.map f w) = Albert.map f (longRootFormula w) := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [longRootFormula, Albert.map]
  · funext i j
    fin_cases i <;> fin_cases j <;> simp [longRootFormula, Albert.map]

private theorem traceZeroMap_add (f : F →+* R) (u v : TraceZero F) :
    traceZeroMap f (u + v) = traceZeroMap f u + traceZeroMap f v := by
  apply Subtype.ext
  exact Albert.map_add f u.val v.val

theorem longRootImage_map (f : F →+* R) (i : TraceZeroCoordinate) :
    traceZeroMap f (longRootImage i) = longRootImage i := by
  rcases i with i | ⟨b,j⟩
  · fin_cases i <;> simp [longRootImage, traceZeroMap_add,
      diagonalVector_map, rootVector_map]
  · fin_cases b <;> fin_cases j <;> simp [longRootImage, traceZeroMap_add,
      diagonalVector_map, rootVector_map]

private def markedVector (i : TraceZeroCoordinate) : TraceZero F :=
  match i with
  | .inl j => diagonalVector (Fin.castLE (by decide) j)
  | .inr r => rootVector r

private theorem markedVector_basis (i : TraceZeroCoordinate) :
    markedVector (F := F) i = markedBasis i := by
  cases i <;> simp only [markedVector, markedBasis_diagonal, markedBasis_root]

private theorem markedVector_map (f : F →+* R) (i : TraceZeroCoordinate) :
    traceZeroMap f (markedVector i) = markedVector i := by
  cases i <;> simp only [markedVector, diagonalVector_map, rootVector_map]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
-- A finite linear-algebra table, not a group certificate.
private theorem longRootFormula_binary : ∀ i : TraceZeroCoordinate,
    longRootFormula (markedVector (F := ZMod 2) i).val =
      (longRootImage (F := ZMod 2) i).val := by decide

theorem longRootCoordinateLinear_eq :
    longRootCoordinateLinear (F := F) = longRootLinear := by
  apply markedBasis.ext
  intro i
  rw [longRootLinear_basis, ← markedVector_basis]
  apply Subtype.ext
  change longRootFormula (markedVector (F := F) i).val = (longRootImage i).val
  let f : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have h := congrArg (Albert.map f) (longRootFormula_binary i)
  rw [← longRootFormula_map] at h
  have hm := congrArg Subtype.val (markedVector_map f i)
  have hi := congrArg Subtype.val (longRootImage_map f i)
  change Albert.map f (markedVector i).val = (markedVector (F := F) i).val at hm
  change Albert.map f (longRootImage i).val = (longRootImage (F := F) i).val at hi
  rw [hm, hi] at h
  exact h

end Atlas.ReeF4
