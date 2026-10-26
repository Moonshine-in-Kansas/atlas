import Atlas.LinearGroups.F4.PointCrossMarked

/-! The second intrinsic cross operator, at the literal C₇ vector. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def pairOppositeVector : Carrier F := (0,![0,0,![0,0,0,0,0,0,0,1]])
def pairOppositeCross : Carrier F →ₗ[F] Carrier F := crossBilinear pairOppositeVector

set_option maxHeartbeats 1200000 in
-- One sparse cross-product matrix, checked in 27 symbolic coordinates.
theorem pairOppositeCross_coordinates (x : Carrier F) :
    pairOppositeCross x =
      (![0,0,-x.2 2 0],
        ![![0,0,0,0,-x.2 1 0,-x.2 1 1,x.2 1 2,-x.2 1 4],
          ![0,0,0,-x.2 0 0,0,x.2 0 1,-x.2 0 2,-x.2 0 3],
          ![0,0,0,0,0,0,0,-x.1 2]]) := by
  apply Prod.ext
  · ext i; fin_cases i <;>
      simp [pairOppositeCross,crossBilinear,pairOppositeVector,cross,adjoint,
        SplitOctonion.norm,Matrix.vecHead,Matrix.vecTail] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [pairOppositeCross,crossBilinear,pairOppositeVector,cross,adjoint,
        SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,
        SplitOctonion.unit,Matrix.vecHead,Matrix.vecTail] <;> ring

end Atlas.F4
