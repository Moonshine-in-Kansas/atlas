import Atlas.LinearGroups.ReeF4.SpecialPoints

/-! Two actual opposite marked special points. No transitivity or point count. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem rootVector_nonzero (r : ShortRootLabel) : (rootVector (F := F) r) ≠ 0 := by
  simpa only [markedBasis_root] using (markedBasis (F := F)).ne_zero (.inr r)

theorem isSpecialVector_firstRoot (m : ℕ) :
    IsSpecialVector m (rootVector (F := F) (0,0)) := by
  have hp : rootDot (scaledShortRoot (0,0)) (scaledShortRoot (0,1)) = 0 := by decide
  refine ⟨rootVector_nonzero _,rootVector (0,1),rootDomain_perpendicular _ _ hp,?_⟩
  rw [proposedPartialProduct_perpendicular (thetaInv F m).toRingHom (0,0) (0,1) hp]
  have ht : starRootTarget (0,0) (0,1) = (0,0) := by decide
  rw [ht]

theorem isSpecialVector_oppositeRoot (m : ℕ) :
    IsSpecialVector m (rootVector (F := F) (0,7)) := by
  have hp : rootDot (scaledShortRoot (0,7)) (scaledShortRoot (0,6)) = 0 := by decide
  refine ⟨rootVector_nonzero _,rootVector (0,6),rootDomain_perpendicular _ _ hp,?_⟩
  rw [proposedPartialProduct_perpendicular (thetaInv F m).toRingHom (0,7) (0,6) hp]
  have ht : starRootTarget (0,7) (0,6) = (0,7) := by decide
  rw [ht]

def firstSpecialPoint (m : ℕ) : SpecialPoints (F := F) m :=
  specialPointMk m (rootVector (0,0)) (isSpecialVector_firstRoot m)

def oppositeSpecialPoint (m : ℕ) : SpecialPoints (F := F) m :=
  specialPointMk m (rootVector (0,7)) (isSpecialVector_oppositeRoot m)

theorem first_opposite_polar :
    traceZeroPolar (rootVector (F := F) (0,0)) (rootVector (0,7)) = 1 := by
  simp [rootPolar,Fin.rev]

end Atlas.ReeF4
