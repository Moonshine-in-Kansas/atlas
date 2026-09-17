import Atlas.Fischer.FischerDoubleCoverTransport
import Atlas.Sporadic.Fischer22
import Atlas.Sporadic.Fischer23

noncomputable section
namespace Atlas.Fischer.DoubleCover22
open Atlas.Codes

/-- The actual ordered double-centralizer quotient, killing the first factor. -/
abbrev ModelAt (i j : Omega) := FischerDoubleCover i j
abbrev Model := ModelAt fischerFirstCoordinate fischerSecondCoordinate
abbrev Points := Atlas.Sporadic.Fischer23.Points
abbrev Target := Atlas.Sporadic.Fischer22.Model

def projection : Model →* Target :=
  doubleCoverProjection fischerFirstCoordinate fischerSecondCoordinate

def centralInvolution : Model :=
  doubleCoverMarkedElement fischerFirstCoordinate fischerSecondCoordinate fischerSecondCoordinate

private theorem coordinates_distinct : fischerFirstCoordinate≠fischerSecondCoordinate := by decide

def centralizerEquiv : Model ≃*
    doubleCoverCentralizerTarget fischerFirstCoordinate fischerSecondCoordinate coordinates_distinct :=
  doubleCoverCentralizerEquiv _ _ coordinates_distinct

def originalAction : Model →* Equiv.Perm Points :=
  doubleCoverOriginalAction _ _ coordinates_distinct

theorem finite : Finite Model := inferInstance
theorem card : Nat.card Model=129123503308800 := doubleCover_order _ _ coordinates_distinct
theorem relative_card : Nat.card Model=2*Nat.card Target := by
  rw [card,Atlas.Sporadic.Fischer22.card]
theorem perfect : Group.IsPerfect Model := doubleCover_perfect _ _ coordinates_distinct
theorem center : Subgroup.center Model=Subgroup.zpowers centralInvolution :=
  doubleCover_center _ _ coordinates_distinct
theorem centralInvolution_order : orderOf centralInvolution=2 :=
  doubleCoverMarkedElement_second_order _ _ coordinates_distinct
theorem projection_surjective : Function.Surjective projection := doubleCoverProjection_surjective _ _
theorem kernel : projection.ker=Subgroup.zpowers centralInvolution :=
  doubleCoverProjection_kernel _ _ coordinates_distinct
theorem kernel_card : Nat.card projection.ker=2 := doubleCoverProjection_kernel_card _ _ coordinates_distinct
theorem nonsplit : ¬ ∃ s : Target →* Model, projection.comp s=MonoidHom.id _ :=
  doubleCoverProjection_nonsplit _ _ coordinates_distinct
theorem faithful : Function.Injective originalAction :=
  doubleCoverOriginalAction_faithful _ _ coordinates_distinct

theorem card_at (i j : Omega) (hij : i≠j) : Nat.card (ModelAt i j)=129123503308800 :=
  doubleCover_order i j hij
theorem perfect_at (i j : Omega) (hij : i≠j) : Group.IsPerfect (ModelAt i j) :=
  doubleCover_perfect i j hij

structure Construction : Prop where
  card : Nat.card Model=129123503308800
  perfect : Group.IsPerfect Model
  center : Subgroup.center Model=Subgroup.zpowers centralInvolution
  kernel : projection.ker=Subgroup.zpowers centralInvolution
  kernel_card : Nat.card projection.ker=2
  surjective : Function.Surjective projection
  nonsplit : ¬ ∃ s : Target →* Model, projection.comp s=MonoidHom.id _
  faithful : Function.Injective originalAction

theorem construction : Construction :=
  ⟨card,perfect,center,kernel,kernel_card,projection_surjective,nonsplit,faithful⟩

end Atlas.Fischer.DoubleCover22
