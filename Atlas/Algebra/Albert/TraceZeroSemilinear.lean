import Atlas.Algebra.Albert.TraceZeroBaseChange

/-! Ring maps act semilinearly on the actual Albert trace kernel. -/
namespace Atlas.Albert
variable {F R : Type*} [CommRing F] [CommRing R]

def traceZeroScalarMap (f : F →+* R) : TraceZero F →ₛₗ[f] TraceZero R where
  toFun := traceZeroMap f
  map_add' u v := by
    apply Subtype.ext
    exact Albert.map_add f u.val v.val
  map_smul' a u := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact f.map_mul _ _
    · funext i j
      exact f.map_mul _ _

@[simp] theorem traceZeroScalarMap_apply (f : F →+* R) (w : TraceZero F) :
    traceZeroScalarMap f w = traceZeroMap f w := rfl

end Atlas.Albert
