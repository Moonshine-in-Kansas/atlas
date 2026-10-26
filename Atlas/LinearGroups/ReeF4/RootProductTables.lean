import Atlas.LinearGroups.ReeF4.RootVectors
import Atlas.LinearGroups.ReeF4.StarDomain
import Atlas.Algebra.Albert.TraceZeroScalarForms

/-! Small, kernel-checked basis tables, transported from the prime field to every
characteristic-two coefficient ring. These are algebra tables, not group certificates. -/
namespace Atlas.ReeF4
open Atlas.Albert

-- Only 24 root labels occur. The finite addition and actual Albert product tables
-- are normalized in the kernel, then transported by the proved scalar-map identities.
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private theorem rootPolar_binary : ∀ r s : ShortRootLabel,
    traceZeroPolar (rootVector (F:=ZMod 2) r) (rootVector s) =
      if s = (r.1, Fin.rev r.2) then 1 else 0 := by decide

private theorem rootCross_opposite_binary : ∀ r : ShortRootLabel,
    traceZeroCross (rootVector (F:=ZMod 2) r) (rootVector (r.1, Fin.rev r.2)) =
      diagonalVector r.1 := by decide

private theorem rootCross_shortSum_binary : ∀ r s t : ShortRootLabel,
    scaledShortRoot r + scaledShortRoot s = scaledShortRoot t →
      traceZeroCross (rootVector (F:=ZMod 2) r) (rootVector s) = rootVector t := by decide

private theorem rootCross_noSum_binary : ∀ r s : ShortRootLabel,
    s ≠ (r.1, Fin.rev r.2) →
    (∀ t, scaledShortRoot r + scaledShortRoot s ≠ scaledShortRoot t) →
      traceZeroCross (rootVector (F:=ZMod 2) r) (rootVector s) = 0 := by
  intro r s
  fin_cases r <;> fin_cases s <;> decide

private theorem rootDomain_perpendicular_binary : ∀ r s : ShortRootLabel,
    rootDot (scaledShortRoot r) (scaledShortRoot s) = 0 →
      StarDomain (rootVector (F:=ZMod 2) r) (rootVector s) := by
  unfold StarDomain
  decide

variable {F : Type*} [CommRing F] [CharP F 2]

theorem rootPolar (r s : ShortRootLabel) :
    traceZeroPolar (rootVector (F:=F) r) (rootVector s) =
      if s = (r.1, Fin.rev r.2) then 1 else 0 := by
  let f : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have h := congrArg f (rootPolar_binary r s)
  rw [← traceZeroMap_polar, rootVector_map, rootVector_map] at h
  simpa only [apply_ite, f.map_one, f.map_zero] using h

theorem rootCross_opposite (r : ShortRootLabel) :
    traceZeroCross (rootVector (F:=F) r) (rootVector (r.1, Fin.rev r.2)) =
      diagonalVector r.1 := by
  let f : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have h := congrArg (traceZeroMap f) (rootCross_opposite_binary r)
  simpa only [← traceZeroMap_cross, rootVector_map, diagonalVector_map] using h

theorem rootCross_shortSum (r s t : ShortRootLabel)
    (hs : scaledShortRoot r + scaledShortRoot s = scaledShortRoot t) :
    traceZeroCross (rootVector (F:=F) r) (rootVector s) = rootVector t := by
  let f : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have h := congrArg (traceZeroMap f) (rootCross_shortSum_binary r s t hs)
  simpa only [← traceZeroMap_cross, rootVector_map] using h

theorem rootCross_noSum (r s : ShortRootLabel) (ho : s ≠ (r.1, Fin.rev r.2))
    (hs : ∀ t, scaledShortRoot r + scaledShortRoot s ≠ scaledShortRoot t) :
    traceZeroCross (rootVector (F:=F) r) (rootVector s) = 0 := by
  let f : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have h := congrArg (traceZeroMap f) (rootCross_noSum_binary r s ho hs)
  simpa only [← traceZeroMap_cross, rootVector_map, traceZeroMap_zero] using h

theorem rootDomain_perpendicular (r s : ShortRootLabel)
    (hs : rootDot (scaledShortRoot r) (scaledShortRoot s) = 0) :
    StarDomain (rootVector (F:=F) r) (rootVector s) := by
  let f : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  obtain ⟨hb,hc⟩ := rootDomain_perpendicular_binary r s hs
  constructor
  · have h := congrArg f hb
    simpa only [← traceZeroMap_polar, rootVector_map, f.map_zero] using h
  · have h := congrArg (traceZeroMap f) hc
    simpa only [← traceZeroMap_cross, rootVector_map, traceZeroMap_zero] using h

end Atlas.ReeF4
