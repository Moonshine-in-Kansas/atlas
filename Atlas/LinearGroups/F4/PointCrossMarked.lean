import Atlas.Algebra.Albert.CrossProduct
import Atlas.Algebra.Albert.Coordinates
import Atlas.Algebra.SplitOctonion.AnnihilatorCharts

/-! The coordinate filtration at C₀. This marking is deliberately distinguished
from the A₀ base point in WhiteZeroPoints. No Levi or Spin identification is assumed. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

/-- The marked trace-zero rank-one vector in the C slot. -/
def parabolicVector : Carrier F := (0,![0,0,![1,0,0,0,0,0,0,0]])

def parabolicCross : Carrier F →ₗ[F] Carrier F := crossBilinear parabolicVector

set_option maxHeartbeats 1200000 in
-- The 27 entries of one sparse cross-product matrix are checked symbolically.
theorem parabolicCross_coordinates (x : Carrier F) :
    parabolicCross x =
      (![0,0,-x.2 2 7],
        ![![-x.2 1 3,x.2 1 5,-x.2 1 6,-x.2 1 7,0,0,0,0],
          ![-x.2 0 4,-x.2 0 5,x.2 0 6,0,-x.2 0 7,0,0,0],
          ![-x.1 2,0,0,0,0,0,0,0]]) := by
  apply Prod.ext
  · ext i; fin_cases i <;>
      simp [parabolicCross,crossBilinear,parabolicVector,cross,adjoint,
        SplitOctonion.norm,Matrix.vecHead,Matrix.vecTail] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [parabolicCross,crossBilinear,parabolicVector,cross,adjoint,
        SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,
        SplitOctonion.unit,Matrix.vecHead,Matrix.vecTail] <;> ring

theorem parabolicCross_eq_zero_iff (x : Carrier F) :
    parabolicCross x=0 ↔ x.1 2=0 ∧ x.2 0 4=0 ∧ x.2 0 5=0 ∧ x.2 0 6=0 ∧
      x.2 0 7=0 ∧ x.2 1 3=0 ∧ x.2 1 5=0 ∧ x.2 1 6=0 ∧ x.2 1 7=0 ∧ x.2 2 7=0 := by
  rw [parabolicCross_coordinates]
  simp [Prod.ext_iff,funext_iff,Fin.forall_fin_succ]
  tauto

end Atlas.F4
