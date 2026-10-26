import Atlas.LinearGroups.Chevalley.RootData.PositiveIntegralRootCone

/-! Positive-root subsets closed under the strict integral cones that occur
in actual root-group commutators. This predicate concerns root data only. -/
noncomputable section
namespace Atlas.Chevalley.RootData
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

def PositiveRootConeClosed (S : Set {β : ι // b.IsPos β}) : Prop :=
  ∀ α ∈ S, ∀ β ∈ S, ∀ γ : {β : ι // b.IsPos β},
    PositiveIntegralRootCone P b α.val β.val γ.val → γ ∈ S

theorem positiveRootConeClosed_univ : PositiveRootConeClosed P b Set.univ := by
  intro α hα β hβ γ hγ
  exact Set.mem_univ γ

theorem positiveRootConeClosed_inter
    {S T : Set {β : ι // b.IsPos β}}
    (hS : PositiveRootConeClosed P b S) (hT : PositiveRootConeClosed P b T) :
    PositiveRootConeClosed P b (S ∩ T) := by
  intro α hα β hβ γ hγ
  exact ⟨hS α hα.1 β hβ.1 γ hγ,hT α hα.2 β hβ.2 γ hγ⟩

end Atlas.Chevalley.RootData
