import Atlas.LinearGroups.ReeF4.StarWedgeEvaluation
import Atlas.LinearGroups.ReeF4.LongRootPairWitness

/-! Local compatibility at the actual pair detecting the extension direction.
This does not replace preservation at all domain pairs. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

theorem wedge_add_left (u v w : TraceZero F) : wedge (u+v) w = wedge u w + wedge v w := by
  exact (exteriorPower.ιMulti F 2).map_vecCons_add ![w] u v

theorem wedge_add_right (u v w : TraceZero F) : wedge u (v+w) = wedge u v + wedge u w := by
  rw [wedge_comm_charTwo, wedge_add_left, wedge_comm_charTwo v u, wedge_comm_charTwo w u]

private theorem root_root (r s : ShortRootLabel) :
    proposedStarLinear (wedge (rootVector (F := F) r) (rootVector s)) =
      extensionCoefficient (.inr r) (.inr s) := by
  rw [← markedBasis_root r, ← markedBasis_root s, proposedStarLinear_marked_wedge]

private theorem diag_zero_root (r : ShortRootLabel) :
    proposedStarLinear (wedge (diagonalVector (F := F) 0) (rootVector r)) = 0 := by
  simpa [markedBasis_diagonal, markedBasis_root, extensionCoefficient] using
    proposedStarLinear_marked_wedge (F := F) (.inl 0) (.inr r)

private theorem diag_one_root (r : ShortRootLabel) :
    proposedStarLinear (wedge (diagonalVector (F := F) 1) (rootVector r)) = 0 := by
  simpa [markedBasis_diagonal, markedBasis_root, extensionCoefficient] using
    proposedStarLinear_marked_wedge (F := F) (.inl 1) (.inr r)

private theorem root_diag_zero (r : ShortRootLabel) :
    proposedStarLinear (wedge (rootVector (F := F) r) (diagonalVector 0)) = 0 := by
  rw [wedge_comm_charTwo, diag_zero_root]

private theorem root_diag_one (r : ShortRootLabel) :
    proposedStarLinear (wedge (rootVector (F := F) r) (diagonalVector 1)) = 0 := by
  rw [wedge_comm_charTwo, diag_one_root]

private theorem diag_pair :
    proposedStarLinear (wedge (diagonalVector (F := F) 0) (diagonalVector 1)) =
      diagonalVector 1 := by
  simpa [markedBasis_diagonal, extensionCoefficient] using
    proposedStarLinear_marked_wedge (F := F) (.inl 0) (.inl 1)

theorem proposedStar_forcing_zero : proposedStarLinear (wedge forcingLeft forcingRight) = 0 := by
  simp only [forcingLeft, forcingRight, wedge_add_left, wedge_add_right, _root_.map_add,
    root_root, diag_zero_root, zero_add]
  decide

set_option maxRecDepth 8192 in
theorem proposedStar_forcing_image_zero :
    proposedStarLinear (wedge forcingLeftImage forcingRightImage) = 0 := by
  simp only [forcingLeftImage, forcingRightImage, longRootImage, wedge_add_left, wedge_add_right,
    _root_.map_add, root_root, diag_zero_root, diag_one_root, root_diag_zero, root_diag_one, diag_pair,
    zero_add, add_zero]
  decide

theorem proposedStar_forcing_compatibility :
    proposedStarLinear (wedge forcingLeftImage forcingRightImage) =
      longRootLinear (proposedStarLinear (wedge forcingLeft forcingRight)) := by
  rw [proposedStar_forcing_zero, proposedStar_forcing_image_zero, _root_.map_zero]

end Atlas.ReeF4
