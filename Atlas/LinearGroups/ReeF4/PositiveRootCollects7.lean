import Atlas.LinearGroups.ReeF4.PositiveRootFactorList
noncomputable section
namespace Atlas.ReeF4
open Atlas.GroupTheory
open scoped Pointwise
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
set_option maxRecDepth 8192 in
theorem positiveRoot_collects_7 {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    CollectsBefore (alternatingLongRootHom hcard 3).range [] := by
  intro x hx J hJ y hy
  cases hJ
end Atlas.ReeF4
