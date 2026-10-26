import Atlas.LinearGroups.ReeF4.RootProductTables

/-! The dependent diagonal labels, including the correction to the zero-label
trilinear entry in the printed source. -/
namespace Atlas.ReeF4
open Atlas.Albert
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

private theorem diagonalPolar_binary : ∀ i j : Fin 3,
    traceZeroPolar (diagonalVector (F:=ZMod 2) i) (diagonalVector j) =
      if i = j then 0 else 1 := by decide

private theorem diagonalRootPolar_binary : ∀ (i : Fin 3) (r : ShortRootLabel),
    traceZeroPolar (diagonalVector (F:=ZMod 2) i) (rootVector r) = 0 := by decide

private theorem diagonalCross_binary : ∀ i j : Fin 3,
    traceZeroCross (diagonalVector (F:=ZMod 2) i) (diagonalVector j) = 0 := by decide

private theorem diagonalRootCross_binary : ∀ (i : Fin 3) (r : ShortRootLabel),
    traceZeroCross (diagonalVector (F:=ZMod 2) i) (rootVector r) =
      if i = r.1 then 0 else rootVector r := by decide

variable {F : Type*} [CommRing F] [CharP F 2]

theorem diagonalPolar (i j : Fin 3) :
    traceZeroPolar (diagonalVector (F:=F) i) (diagonalVector j) =
      if i = j then 0 else 1 := by
  let f : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have h := congrArg f (diagonalPolar_binary i j)
  rw [← traceZeroMap_polar, diagonalVector_map, diagonalVector_map] at h
  simpa only [apply_ite, f.map_one, f.map_zero] using h

theorem diagonalRootPolar (i : Fin 3) (r : ShortRootLabel) :
    traceZeroPolar (diagonalVector (F:=F) i) (rootVector r) = 0 := by
  let f : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have h := congrArg f (diagonalRootPolar_binary i r)
  simpa only [← traceZeroMap_polar, diagonalVector_map, rootVector_map, f.map_zero] using h

theorem diagonalCross (i j : Fin 3) :
    traceZeroCross (diagonalVector (F:=F) i) (diagonalVector j) = 0 := by
  let f : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have h := congrArg (traceZeroMap f) (diagonalCross_binary i j)
  simpa only [← traceZeroMap_cross, diagonalVector_map, traceZeroMap_zero] using h

theorem diagonalRootCross (i : Fin 3) (r : ShortRootLabel) :
    traceZeroCross (diagonalVector (F:=F) i) (rootVector r) =
      if i = r.1 then 0 else rootVector r := by
  let f : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have h := congrArg (traceZeroMap f) (diagonalRootCross_binary i r)
  simpa only [← traceZeroMap_cross, diagonalVector_map, rootVector_map,
    apply_ite, traceZeroMap_zero] using h

theorem diagonalTrilinear_zero (i j k : Fin 3) :
    traceZeroPolar (traceZeroCross (diagonalVector (F:=F) i) (diagonalVector j))
      (diagonalVector (F:=F) k) = 0 := by
  rw [diagonalCross]
  change tracePairing (0 : Carrier F) (diagonalVector (F:=F) k : Carrier F) = 0
  simp [tracePairing, trace, quadraticTrace, SplitOctonion.norm]

end Atlas.ReeF4
