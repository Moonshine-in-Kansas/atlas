import Atlas.Algebra.Albert.ShortRootMaps

/-! Sparse coordinate formulas for the two first-pair short roots used by
the rank-one torus words. Their equalities are symbolic ring identities. -/
namespace Atlas.F4
variable {R : Type*} [CommRing R]

def torusShortApply3 (t : R) (x : Atlas.Albert.Carrier R) : Atlas.Albert.Carrier R :=
  (![x.1 0 - t*x.2 2 4,x.1 1 + t*x.2 2 4,x.1 2],![![x.2 0 0,x.2 0 1 - t*x.2 1 1,x.2 0 2 - t*x.2 1 2,x.2 0 3,x.2 0 4 + t*x.2 1 3,x.2 0 5,x.2 0 6,x.2 0 7 - t*x.2 1 7],![x.2 1 0 + t*x.2 0 0,x.2 1 1,x.2 1 2,x.2 1 3,x.2 1 4 - t*x.2 0 3,x.2 1 5 + t*x.2 0 5,x.2 1 6 + t*x.2 0 6,x.2 1 7],![x.2 2 0,x.2 2 1,x.2 2 2,x.2 2 3 + t*x.1 0 - t*x.1 1 - t^2*x.2 2 4,x.2 2 4,x.2 2 5,x.2 2 6,x.2 2 7]])

set_option maxHeartbeats 800000 in
-- Expand one sparse root once, before composing rank-one words.
theorem shortRootLinear_torusShortApply3 (t : R) (x : Atlas.Albert.Carrier R) :
    Atlas.Albert.shortRootLinear 3 t x=torusShortApply3 t x := by
  apply Prod.ext
  · ext j; fin_cases j <;>
      simp [torusShortApply3,Atlas.Albert.shortRootLinear,Atlas.Albert.shortRootFormula,
        Atlas.SplitOctonion.basisVector,Pi.single_apply,Atlas.SplitOctonion.mul,
        Atlas.SplitOctonion.conjugate,Atlas.SplitOctonion.trace,Atlas.SplitOctonion.unit,
        Matrix.vecHead,Matrix.vecTail] <;> ring
  · ext j k; fin_cases j <;> fin_cases k <;>
      simp [torusShortApply3,Atlas.Albert.shortRootLinear,Atlas.Albert.shortRootFormula,
        Atlas.SplitOctonion.basisVector,Pi.single_apply,Atlas.SplitOctonion.mul,
        Atlas.SplitOctonion.conjugate,Atlas.SplitOctonion.trace,Atlas.SplitOctonion.unit,
        Matrix.vecHead,Matrix.vecTail] <;> ring

def torusShortApply4 (t : R) (x : Atlas.Albert.Carrier R) : Atlas.Albert.Carrier R :=
  (![x.1 0 - t*x.2 2 3,x.1 1 + t*x.2 2 3,x.1 2],![![x.2 0 0 - t*x.2 1 0,x.2 0 1,x.2 0 2,x.2 0 3 + t*x.2 1 4,x.2 0 4,x.2 0 5 - t*x.2 1 5,x.2 0 6 - t*x.2 1 6,x.2 0 7],![x.2 1 0,x.2 1 1 + t*x.2 0 1,x.2 1 2 + t*x.2 0 2,x.2 1 3 - t*x.2 0 4,x.2 1 4,x.2 1 5,x.2 1 6,x.2 1 7 + t*x.2 0 7],![x.2 2 0,x.2 2 1,x.2 2 2,x.2 2 3,x.2 2 4 + t*x.1 0 - t*x.1 1 - t^2*x.2 2 3,x.2 2 5,x.2 2 6,x.2 2 7]])

set_option maxHeartbeats 800000 in
-- Expand one sparse root once, before composing rank-one words.
theorem shortRootLinear_torusShortApply4 (t : R) (x : Atlas.Albert.Carrier R) :
    Atlas.Albert.shortRootLinear 4 t x=torusShortApply4 t x := by
  apply Prod.ext
  · ext j; fin_cases j <;>
      simp [torusShortApply4,Atlas.Albert.shortRootLinear,Atlas.Albert.shortRootFormula,
        Atlas.SplitOctonion.basisVector,Pi.single_apply,Atlas.SplitOctonion.mul,
        Atlas.SplitOctonion.conjugate,Atlas.SplitOctonion.trace,Atlas.SplitOctonion.unit,
        Matrix.vecHead,Matrix.vecTail] <;> ring
  · ext j k; fin_cases j <;> fin_cases k <;>
      simp [torusShortApply4,Atlas.Albert.shortRootLinear,Atlas.Albert.shortRootFormula,
        Atlas.SplitOctonion.basisVector,Pi.single_apply,Atlas.SplitOctonion.mul,
        Atlas.SplitOctonion.conjugate,Atlas.SplitOctonion.trace,Atlas.SplitOctonion.unit,
        Matrix.vecHead,Matrix.vecTail] <;> ring

end Atlas.F4
