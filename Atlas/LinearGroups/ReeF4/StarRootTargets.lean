import Atlas.LinearGroups.ReeF4.HurwitzRoots

/-! The inverse-dilation rule for perpendicular short-root labels. -/
namespace Atlas.ReeF4

def rootLabels : List ShortRootLabel :=
  (List.finRange 3).flatMap fun i => (List.finRange 8).map fun j => (i,j)

def starRootTarget (r s : ShortRootLabel) : ShortRootLabel :=
  ((rootLabels.find? fun t => decide
    (rootPhi (scaledShortRoot t) = scaledShortRoot r + scaledShortRoot s))).getD (0,0)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- This is the complete finite table on the 24 labelled roots, checked by the kernel.
theorem starRootTarget_spec : ∀ r s : ShortRootLabel,
    rootDot (scaledShortRoot r) (scaledShortRoot s) = 0 →
    rootPhi (scaledShortRoot (starRootTarget r s)) =
      scaledShortRoot r + scaledShortRoot s := by decide

theorem starRootTarget_unique (r s t : ShortRootLabel)
    (hp : rootDot (scaledShortRoot r) (scaledShortRoot s) = 0)
    (ht : rootPhi (scaledShortRoot t) = scaledShortRoot r + scaledShortRoot s) :
    starRootTarget r s = t := by
  apply scaledShortRoot_injective
  apply rootPhi_injective
  exact (starRootTarget_spec r s hp).trans ht.symm

theorem starRootTarget_comm (r s : ShortRootLabel)
    (hp : rootDot (scaledShortRoot r) (scaledShortRoot s) = 0) :
    starRootTarget r s = starRootTarget s r := by
  apply starRootTarget_unique r s _ hp
  have hs : rootDot (scaledShortRoot s) (scaledShortRoot r) = 0 := by
    simpa [rootDot, mul_comm] using hp
  simpa [add_comm] using starRootTarget_spec s r hs

end Atlas.ReeF4
