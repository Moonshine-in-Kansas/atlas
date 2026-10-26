import Atlas.Algebra.Albert.OppositeChart
import Atlas.Algebra.Albert.UniversalCriterion

/-! Twenty-four explicit integral combinations of opposite-cell vectors recover
all octonion-coordinate basis vectors. The certificates are independent of group order. -/
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def cellOrigin : Carrier F := oppositeZeroChart 0 0 0 0
def cellU (i : Fin 4) : Carrier F := oppositeZeroChart 0 (Pi.single i 1) 0 0
def cellV (i : Fin 4) : Carrier F := oppositeZeroChart 0 0 (Pi.single i 1) 0
def cellZ (i : Fin 6) : Carrier F := oppositeZeroChart 0 0 0 (Pi.single i 1)
def cellUZ (i : Fin 4) (j : Fin 6) : Carrier F :=
  oppositeZeroChart 0 (Pi.single i 1) 0 (Pi.single j 1)-cellU i-cellZ j+cellOrigin
def cellVZ (i : Fin 4) (j : Fin 6) : Carrier F :=
  oppositeZeroChart 0 0 (Pi.single i 1) (Pi.single j 1)-cellV i-cellZ j+cellOrigin
def cellZZ : Carrier F :=
  oppositeZeroChart 0 0 0 (Pi.single 0 1+Pi.single 5 1)-cellZ 0-cellZ 5+cellOrigin

def oppositeOffCombination : Fin 3→Fin 8→Carrier F :=
  ![![cellUZ 0 3,cellUZ 0 4,-cellUZ 0 5,cellUZ 1 5,
      cellU 0-cellOrigin,cellU 1-cellOrigin,cellU 2-cellOrigin,cellU 3-cellOrigin],
    ![cellVZ 0 2,-cellVZ 0 4,cellVZ 0 5,cellV 0-cellOrigin,
      -cellVZ 1 5,cellV 1-cellOrigin,cellV 2-cellOrigin,cellV 3-cellOrigin],
    ![-cellZZ,cellZ 0-cellOrigin,cellZ 1-cellOrigin,cellZ 2-cellOrigin,
      cellZ 3-cellOrigin,cellZ 4-cellOrigin,cellZ 5-cellOrigin,cellOrigin]]

set_option maxHeartbeats 1500000 in
-- Reduce each of the 24 selected chart expressions once before splitting coordinates.
theorem oppositeOffCombination_basis (i : Fin 3) (j : Fin 8) :
    oppositeOffCombination (F:=F) i j = basisVector (.inr (i,j)) := by
  fin_cases i <;> fin_cases j
  all_goals
    dsimp only [oppositeOffCombination]
    simp [cellOrigin,cellU,cellV,cellZ,cellUZ,cellVZ,cellZZ,
      oppositeZeroChart,oppositeChart,oppositeDiagonalC,oppositeA,oppositeB,oppositeC,
      Pi.single_apply,Matrix.vecHead,Matrix.vecTail]
  all_goals
    apply Prod.ext
    · ext k; fin_cases k <;> simp [basisVector]
    · ext k l; fin_cases k <;> fin_cases l <;> simp [basisVector]

end Atlas.F4
