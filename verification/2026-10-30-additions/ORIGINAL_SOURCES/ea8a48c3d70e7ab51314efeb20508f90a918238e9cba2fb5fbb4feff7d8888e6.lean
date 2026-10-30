import F4Work.F4IntegralSparseGeckRoot0
import F4Work.F4IntegralSparseGeckRoot1
import F4Work.F4IntegralSparseGeckRoot2
import F4Work.F4IntegralSparseGeckRoot3
import F4Work.F4IntegralSparseGeckRoot4
import F4Work.F4IntegralSparseGeckRoot5
import F4Work.F4IntegralSparseGeckRoot6
import F4Work.F4IntegralSparseGeckRoot7

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
