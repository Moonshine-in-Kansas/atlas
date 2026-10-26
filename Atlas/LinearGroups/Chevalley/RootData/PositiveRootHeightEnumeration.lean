import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Sort

/-! A finite exhaustive positive-root list sorted by height. Equal-height
ties retain an arbitrary initial enumeration; no root-order convexity is asserted. -/
noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

def positiveRootHeightList : List {β : ι // b.IsPos β} :=
  (Finset.univ : Finset {β : ι // b.IsPos β}).toList.mergeSort
    (fun β γ => decide (b.height β.val ≤ b.height γ.val))

theorem positiveRootHeightList_nodup : (positiveRootHeightList P b).Nodup := by
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

theorem positiveRootHeightList_pairwise :
    (positiveRootHeightList P b).Pairwise
      (fun β γ => b.height β.val ≤ b.height γ.val) := by
  let r : {β : ι // b.IsPos β} → {β : ι // b.IsPos β} → Prop :=
    fun β γ => b.height β.val ≤ b.height γ.val
  letI heightTotal : Std.Total r := ⟨fun β γ => le_total _ _⟩
  letI heightTrans : IsTrans {β : ι // b.IsPos β} r :=
    ⟨fun β γ δ hβγ hγδ => le_trans hβγ hγδ⟩
  exact List.pairwise_mergeSort' r _

theorem mem_positiveRootHeightList (β : {β : ι // b.IsPos β}) :
    β ∈ positiveRootHeightList P b := by
  apply (List.mergeSort_perm _ _).mem_iff.mpr
  exact Finset.mem_toList.mpr (Finset.mem_univ β)

theorem positiveRootHeightList_length :
    (positiveRootHeightList P b).length = Fintype.card {β : ι // b.IsPos β} := by
  calc
    (positiveRootHeightList P b).length =
        (Finset.univ : Finset {β : ι // b.IsPos β}).toList.length :=
      (List.mergeSort_perm _ _).length_eq
    _ = _ := by rw [Finset.length_toList, Finset.card_univ]

end Atlas.Chevalley.RootData
