import Atlas.LinearGroups.Chevalley.Comparison.F4.GeckOperatorsRoot0
import Atlas.LinearGroups.Chevalley.Comparison.F4.GeckOperatorsRoot1
import Atlas.LinearGroups.Chevalley.Comparison.F4.GeckOperatorsRoot2
import Atlas.LinearGroups.Chevalley.Comparison.F4.GeckOperatorsRoot3

noncomputable section
namespace Atlas.Chevalley.Comparison.F4
open Classical Integral F4Data
open scoped Matrix
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem E_numeric_table : ∀ (k : Fin 4) (a c : Fin 52),
    E k ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm a)
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) =
      geckMatrix (Fin.castAdd 4 k) a c := by
  intro k a c
  fin_cases k
  · exact E_numeric_table_root0 a c
  · exact E_numeric_table_root1 a c
  · exact E_numeric_table_root2 a c
  · exact E_numeric_table_root3 a c

theorem reindex52_raising (k : Fin 4) :
    reindex52 ℤ (raising pairing base (baseIndexEquiv k)) =
      geckMatrix (Fin.castAdd 4 k) := by
  ext a c
  have h := congrArg (fun M : Matrix I I ℤ =>
    M ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm a)
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c)) (reindex_raising k)
  exact h.trans (E_numeric_table k a c)

end Atlas.Chevalley.Comparison.F4
