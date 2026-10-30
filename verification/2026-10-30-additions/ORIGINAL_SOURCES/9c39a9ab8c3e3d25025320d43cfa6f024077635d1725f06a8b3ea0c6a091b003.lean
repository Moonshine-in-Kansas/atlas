import F4Work.F4IntegralSparseGeckSecondRoot0
import F4Work.F4IntegralSparseGeckSecondRoot1
import F4Work.F4IntegralSparseGeckSecondRoot2
import F4Work.F4IntegralSparseGeckSecondRoot3
import F4Work.F4IntegralSparseGeckSecondRoot4
import F4Work.F4IntegralSparseGeckSecondRoot5
import F4Work.F4IntegralSparseGeckSecondRoot6
import F4Work.F4IntegralSparseGeckSecondRoot7

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
