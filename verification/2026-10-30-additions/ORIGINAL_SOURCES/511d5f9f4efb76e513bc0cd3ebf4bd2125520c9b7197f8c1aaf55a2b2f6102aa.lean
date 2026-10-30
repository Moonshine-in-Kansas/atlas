import F4Work.F4IntegralSparseTables

/-! Finite matrix checks are separated by their outer index to bound reduction memory. -/
namespace Atlas.Chevalley.Comparison.F4
open Atlas.LinearAlgebra.SparseIntegralMatrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

private theorem denote_simpleSecondEntries_0 :
    denote (simpleSecondEntries 0) = simpleSecondMatrix 0 := by
  decide +kernel

private theorem denote_simpleSecondEntries_1 :
    denote (simpleSecondEntries 1) = simpleSecondMatrix 1 := by
  decide +kernel

private theorem denote_simpleSecondEntries_2 :
    denote (simpleSecondEntries 2) = simpleSecondMatrix 2 := by
  decide +kernel

private theorem denote_simpleSecondEntries_3 :
    denote (simpleSecondEntries 3) = simpleSecondMatrix 3 := by
  decide +kernel

private theorem denote_simpleSecondEntries_4 :
    denote (simpleSecondEntries 4) = simpleSecondMatrix 4 := by
  decide +kernel

private theorem denote_simpleSecondEntries_5 :
    denote (simpleSecondEntries 5) = simpleSecondMatrix 5 := by
  decide +kernel

private theorem denote_simpleSecondEntries_6 :
    denote (simpleSecondEntries 6) = simpleSecondMatrix 6 := by
  decide +kernel

private theorem denote_simpleSecondEntries_7 :
    denote (simpleSecondEntries 7) = simpleSecondMatrix 7 := by
  decide +kernel

theorem denote_simpleSecondEntries : ∀ i : Fin 8,
    denote (simpleSecondEntries i)=simpleSecondMatrix i := by
  intro i
  fin_cases i
  · exact denote_simpleSecondEntries_0
  · exact denote_simpleSecondEntries_1
  · exact denote_simpleSecondEntries_2
  · exact denote_simpleSecondEntries_3
  · exact denote_simpleSecondEntries_4
  · exact denote_simpleSecondEntries_5
  · exact denote_simpleSecondEntries_6
  · exact denote_simpleSecondEntries_7

end Atlas.Chevalley.Comparison.F4
