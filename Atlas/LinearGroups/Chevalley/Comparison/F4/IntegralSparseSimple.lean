import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseTables

/-! Finite matrix checks are separated by their outer index to bound reduction memory. -/
namespace Atlas.Chevalley.Comparison.F4
open Atlas.LinearAlgebra.SparseIntegralMatrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

private theorem denote_simpleEntries_0 :
    denote (simpleEntries 0) = simpleMatrix 0 := by
  decide +kernel

private theorem denote_simpleEntries_1 :
    denote (simpleEntries 1) = simpleMatrix 1 := by
  decide +kernel

private theorem denote_simpleEntries_2 :
    denote (simpleEntries 2) = simpleMatrix 2 := by
  decide +kernel

private theorem denote_simpleEntries_3 :
    denote (simpleEntries 3) = simpleMatrix 3 := by
  decide +kernel

private theorem denote_simpleEntries_4 :
    denote (simpleEntries 4) = simpleMatrix 4 := by
  decide +kernel

private theorem denote_simpleEntries_5 :
    denote (simpleEntries 5) = simpleMatrix 5 := by
  decide +kernel

private theorem denote_simpleEntries_6 :
    denote (simpleEntries 6) = simpleMatrix 6 := by
  decide +kernel

private theorem denote_simpleEntries_7 :
    denote (simpleEntries 7) = simpleMatrix 7 := by
  decide +kernel

theorem denote_simpleEntries : ∀ i : Fin 8, denote (simpleEntries i)=simpleMatrix i := by
  intro i
  fin_cases i
  · exact denote_simpleEntries_0
  · exact denote_simpleEntries_1
  · exact denote_simpleEntries_2
  · exact denote_simpleEntries_3
  · exact denote_simpleEntries_4
  · exact denote_simpleEntries_5
  · exact denote_simpleEntries_6
  · exact denote_simpleEntries_7

end Atlas.Chevalley.Comparison.F4
