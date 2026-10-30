import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseGeckSecondRoot0
import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseGeckSecondRoot1
import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseGeckSecondRoot2
import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseGeckSecondRoot3
import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseGeckSecondRoot4
import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseGeckSecondRoot5
import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseGeckSecondRoot6
import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralSparseGeckSecondRoot7

namespace Atlas.Chevalley.Comparison.F4
open Atlas.LinearAlgebra.SparseIntegralMatrix

theorem denote_geckSecondEntries : ∀ i : Fin 8,
    denote (geckSecondEntries i)=geckSecondMatrix i := by
  intro i
  funext j k
  fin_cases i
  · exact denote_geckSecondEntries_root0 j k
  · exact denote_geckSecondEntries_root1 j k
  · exact denote_geckSecondEntries_root2 j k
  · exact denote_geckSecondEntries_root3 j k
  · exact denote_geckSecondEntries_root4 j k
  · exact denote_geckSecondEntries_root5 j k
  · exact denote_geckSecondEntries_root6 j k
  · exact denote_geckSecondEntries_root7 j k

end Atlas.Chevalley.Comparison.F4
