import Atlas.Algebra.Albert.RankOneChart
import Mathlib.FieldTheory.Finite.Basic

namespace Atlas.Albert
variable {F : Type*} [Field F] [Finite F]

/-- Independent geometric count of the first diagonal open rank-one chart. -/
theorem card_rankOne_first_diagonal :
    Nat.card {x : Carrier F // adjoint x = 0 ∧ x.1 0 ≠ 0} =
      (Nat.card F - 1) * Nat.card F ^ 16 := by
  rw [← Nat.card_congr (rankOneChartEquiv (F := F))]
  simp only [Nat.card_prod, Nat.card_units, SplitOctonion.Carrier,
    Nat.card_fun, Nat.card_fin, ← pow_add]

end Atlas.Albert
