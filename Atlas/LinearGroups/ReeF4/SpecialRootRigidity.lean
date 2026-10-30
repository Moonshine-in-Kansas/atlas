import Atlas.LinearGroups.ReeF4.SpecialMarkedPoints
import Atlas.LinearGroups.ReeF4.SixVectorRigidity

/-!
Source-only draft. Six explicitly special marked roots determine an intrinsic
model element. The two nonspecial roots in the inherited six-vector rigidity
criterion are recovered by actual Albert cross products.
No field-cardinality, full-order, generation, or simplicity result is used.
No Lean, Lake, checker, audit, or enumeration was run for this draft.
-/

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A concrete perpendicular witness whose inverse-dilation target is the left
root proves that root special. The target is identified by uniqueness, without
evaluating the root-label search. -/
theorem isSpecialVector_root_of_perpendicular_phi (m : ℕ) (r s : ShortRootLabel)
    (hp : rootDot (scaledShortRoot r) (scaledShortRoot s) = 0)
    (hphi : rootPhi (scaledShortRoot r) = scaledShortRoot r + scaledShortRoot s) :
    IsSpecialVector m (rootVector (F := F) r) := by
  have hn : (rootVector (F := F) r) ≠ 0 := by
    simpa only [markedBasis_root] using (markedBasis (F := F)).ne_zero (.inr r)
  refine ⟨hn, rootVector s, rootDomain_perpendicular r s hp, ?_⟩
  rw [proposedPartialProduct_perpendicular (thetaInv F m).toRingHom r s hp,
    starRootTarget_unique r s r hp hphi]

/-- Flat root coordinate 4; the partial-product witness is root (0,3). -/
theorem isSpecialVector_root_zero_two (m : ℕ) :
    IsSpecialVector m (rootVector (F := F) (0,2)) :=
  isSpecialVector_root_of_perpendicular_phi m (0,2) (0,3) (by decide) (by decide)

/-- Flat root coordinate 7; the partial-product witness is root (0,4). -/
theorem isSpecialVector_root_zero_five (m : ℕ) :
    IsSpecialVector m (rootVector (F := F) (0,5)) :=
  isSpecialVector_root_of_perpendicular_phi m (0,5) (0,4) (by decide) (by decide)

/-- Flat root coordinate 18; the partial-product witness is root (2,2). -/
theorem isSpecialVector_root_two_zero (m : ℕ) :
    IsSpecialVector m (rootVector (F := F) (2,0)) :=
  isSpecialVector_root_of_perpendicular_phi m (2,0) (2,2) (by decide) (by decide)

/-- Flat root coordinate 19; the partial-product witness is root (2,4). -/
theorem isSpecialVector_root_two_one (m : ℕ) :
    IsSpecialVector m (rootVector (F := F) (2,1)) :=
  isSpecialVector_root_of_perpendicular_phi m (2,1) (2,4) (by decide) (by decide)

/-- Fixation propagates along an actual root cross product. This uses polynomial
form preservation from the intrinsic model definition, not generation. -/
theorem model_fixes_root_of_cross_sum {m : ℕ} (g : Model F m)
    (r s t : ShortRootLabel)
    (hr : g.val (rootVector r) = rootVector r)
    (hs : g.val (rootVector s) = rootVector s)
    (hadd : scaledShortRoot r + scaledShortRoot s = scaledShortRoot t) :
    g.val (rootVector t) = rootVector t := by
  obtain ⟨hp, _⟩ := (mem_modelSubgroup_iff m g.val).mp g.property
  have hc := traceZeroCross_of_forms g.val
    (traceZeroStabilizer_quadratic ⟨g.val,hp⟩)
    (traceZeroStabilizer_cubic ⟨g.val,hp⟩) (rootVector r) (rootVector s)
  rw [hr, hs] at hc
  simpa only [rootCross_shortSum r s t hadd] using hc.symm

/-- Only the special roots at flat coordinates 9,2,18,4,7,19 are needed.
Roots (1,0) and (1,1) are recovered by cross products; they are not asserted
special or included among the projective-point hypotheses. -/
theorem model_eq_one_of_fix_six_special_roots {m : ℕ} (g : Model F m)
    (h9 : g.val (rootVector (0,7)) = rootVector (0,7))
    (h2 : g.val (rootVector (0,0)) = rootVector (0,0))
    (h18 : g.val (rootVector (2,0)) = rootVector (2,0))
    (h4 : g.val (rootVector (0,2)) = rootVector (0,2))
    (h7 : g.val (rootVector (0,5)) = rootVector (0,5))
    (h19 : g.val (rootVector (2,1)) = rootVector (2,1)) : g = 1 := by
  have h10 : g.val (rootVector (1,0)) = rootVector (1,0) :=
    model_fixes_root_of_cross_sum g (0,2) (2,1) (1,0) h4 h19 (by decide)
  have h11 : g.val (rootVector (1,1)) = rootVector (1,1) :=
    model_fixes_root_of_cross_sum g (0,5) (2,0) (1,1) h7 h18 (by decide)
  exact model_eq_one_of_fix_six g h9 h2 h18 h10 h11 h19

end Atlas.ReeF4
