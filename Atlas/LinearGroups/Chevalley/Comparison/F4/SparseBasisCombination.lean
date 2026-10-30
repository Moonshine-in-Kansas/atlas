import Atlas.LinearGroups.Chevalley.Comparison.F4.SparseCoefficientSemantics
import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseBasis

/-! Apply the generic coefficient-list semantics to the existing literal
52-element integral matrix family. No new table or independence premise. -/
namespace Atlas.Chevalley.Comparison.F4
open Atlas.LinearAlgebra.SparseIntegralMatrix

/-- Replace the dense `Fin 52` linear combination by the selected sparse
basis-entry lists of its coefficient column. -/
theorem basisCombination_denote_column (L : List (Entry 52)) (j : Fin 52) :
    basisCombination (fun k => denote L k j) =
      denote (columnEntries basisEntries L j) := by
  rw [denote_columnEntries]
  simp only [basisCombination, denote_basisEntries]

end Atlas.Chevalley.Comparison.F4
