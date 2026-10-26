import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionReducedWords
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The Poincare sum of the actual root-permutation Weyl group. No product
formula or type-specific degree list is assumed. -/
noncomputable section
namespace Atlas.Chevalley.RootData
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)
local instance : Fintype P.weylGroupToPerm.range := Fintype.ofFinite _

def rootWeylPoincareEval (q : ℕ) : ℕ :=
  ∑ w : P.weylGroupToPerm.range, q ^ rootWeylLength P b w

end Atlas.Chevalley.RootData
