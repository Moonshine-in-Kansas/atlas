import Atlas.Algebra.Albert.TraceZeroBaseChange

/-! Naturality of the actual trace-zero forms and cross product. -/
namespace Atlas.Albert
variable {F R : Type*} [CommRing F] [CommRing R]

theorem scalarMap_sub (f : F →+* R) (x y : Carrier F) :
    map f (x-y) = map f x - map f y := by
  apply Prod.ext
  · funext i; simp [map]
  · funext i j; simp [map]

theorem cross_scalarMap (f : F →+* R) (x y : Carrier F) :
    cross (map f x) (map f y) = map f (cross x y) := by
  simp only [cross, ← map_add, adjoint_map, scalarMap_sub]

@[simp] theorem traceZeroMap_zero (f : F →+* R) : traceZeroMap f (0 : TraceZero F) = 0 := by
  apply Subtype.ext
  apply Prod.ext
  · funext i; simp [traceZeroMap, map]
  · funext i j; simp [traceZeroMap, map]

variable [CharP F 2] [CharP R 2]

theorem traceZeroMap_cross (f : F →+* R) (u v : TraceZero F) :
    traceZeroCross (traceZeroMap f u) (traceZeroMap f v) =
      traceZeroMap f (traceZeroCross u v) := by
  unfold traceZeroCross
  rw [← traceZeroProjection_map]
  congr 1
  exact cross_scalarMap f u v

theorem traceZeroMap_polar (f : F →+* R) (u v : TraceZero F) :
    traceZeroPolar (traceZeroMap f u) (traceZeroMap f v) = f (traceZeroPolar u v) :=
  tracePairing_map f u v

end Atlas.Albert
