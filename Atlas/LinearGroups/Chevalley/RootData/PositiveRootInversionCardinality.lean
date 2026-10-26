import Atlas.LinearGroups.Chevalley.RootData.PositiveRootWeylPartition
import Mathlib.SetTheory.Cardinal.Finite

/-! The positive-subtype inversion set has the actual Weyl word length.
This is root combinatorics only, with no group-cardinality input. -/
noncomputable section
namespace Atlas.Chevalley.RootData
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

theorem positiveRootInversionSubset_card (w : P.weylGroupToPerm.range) :
    Nat.card (positiveRootInversionSubset P b w) = rootWeylLength P b w := by
  let e : positiveRootInversionSubset P b w ≃ ↥(rootInversions P b w) :=
    { toFun := fun β => ⟨β.val.val,
        (mem_positiveRootInversionSubset_iff_rootInversions P b w β.val).mp β.property⟩
      invFun := fun β => ⟨⟨β.val, ((mem_rootInversions P b w β.val).mp β.property).1⟩,
        ((mem_rootInversions P b w β.val).mp β.property).2⟩
      left_inv := fun β => rfl
      right_inv := fun β => rfl }
  calc
    Nat.card (positiveRootInversionSubset P b w) = Nat.card ↥(rootInversions P b w) :=
      Nat.card_congr e
    _ = (rootInversions P b w).card := Nat.card_eq_finsetCard _
    _ = rootWeylLength P b w := rootInversionCount_eq_rootWeylLength P b w

end Atlas.Chevalley.RootData
