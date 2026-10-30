import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseGeckRoot0
import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseGeckRoot1
import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseGeckRoot2
import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseGeckRoot3
import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseGeckRoot4
import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseGeckRoot5
import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseGeckRoot6
import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseGeckRoot7

namespace Atlas.Chevalley.Comparison.F4
open Atlas.LinearAlgebra.SparseIntegralMatrix

theorem denote_geckEntries : ∀ i : Fin 8, denote (geckEntries i)=geckMatrix i := by
  intro i
  funext j k
  fin_cases i
  · exact denote_geckEntries_root0 j k
  · exact denote_geckEntries_root1 j k
  · exact denote_geckEntries_root2 j k
  · exact denote_geckEntries_root3 j k
  · exact denote_geckEntries_root4 j k
  · exact denote_geckEntries_root5 j k
  · exact denote_geckEntries_root6 j k
  · exact denote_geckEntries_root7 j k

end Atlas.Chevalley.Comparison.F4
