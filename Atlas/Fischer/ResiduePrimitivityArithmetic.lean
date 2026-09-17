import Atlas.GroupTheory.RankThreePrimitivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace Atlas.Fischer

/-- The three numerical targets, separated from the actual orbit proofs. -/
def fischerRankThreeDegree : Fin 3 → ℕ := ![306936,31671,3510]

def fischerRankThreeSubdegree : Fin 3 → Fin 3 → ℕ :=
  ![![1,31671,275264],![1,3510,28160],![1,693,2816]]

theorem fischerRankThree_singleton (s : Fin 3) : fischerRankThreeSubdegree s 0=1 := by
  fin_cases s <;> rfl

theorem fischerRankThree_degree_sum (s : Fin 3) :
    fischerRankThreeDegree s=1+fischerRankThreeSubdegree s 1+fischerRankThreeSubdegree s 2 := by
  fin_cases s <;> rfl

theorem fischerRankThree_first_nondivisibility (s : Fin 3) :
    ¬(1+fischerRankThreeSubdegree s 1) ∣ fischerRankThreeDegree s := by
  fin_cases s <;> decide

theorem fischerRankThree_second_nondivisibility (s : Fin 3) :
    ¬(1+fischerRankThreeSubdegree s 2) ∣ fischerRankThreeDegree s := by
  fin_cases s <;> decide

end Atlas.Fischer
