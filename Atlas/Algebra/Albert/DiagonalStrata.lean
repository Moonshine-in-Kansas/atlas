import Atlas.Algebra.Albert.RestrictedChartCount
import Atlas.LinearGroups.F4.ShortRoots
import Atlas.Algebra.Albert.StabilizerInvariants

/-! Cyclic identification of the disjoint nonzero diagonal strata. -/
noncomputable section
namespace Atlas.Albert
variable {F : Type*} [Field F]

theorem cycle_adjoint_zero_iff (x : Carrier F) :
    adjoint (coordinateCycle x)=0 ↔ adjoint x=0 := by
  have h := stabilizer_adjoint (Atlas.F4.coordinateCycle (F:=F)) x
  change adjoint (coordinateCycle x)=coordinateCycle (adjoint x) at h
  rw [h]
  exact (coordinateCycleEquiv (F:=F)).map_eq_zero_iff

theorem cycle_trace (x : Carrier F) : trace (coordinateCycle x)=trace x :=
  stabilizer_trace (Atlas.F4.coordinateCycle (F:=F)) x

def secondDiagonalEquiv :
    {x : Carrier F // adjoint x=0 ∧ x.1 0=0 ∧ x.1 1≠0} ≃
    {x : Carrier F // adjoint x=0 ∧ x.1 0≠0 ∧ x.1 2=0} :=
  coordinateCycleEquiv.toEquiv.subtypeEquiv (fun x => by
    change (_ ∧ _ ∧ _) ↔ (adjoint (coordinateCycle x)=0 ∧ _ ∧ _)
    rw [cycle_adjoint_zero_iff]
    change (adjoint x=0 ∧ x.1 0=0 ∧ x.1 1≠0) ↔
      (adjoint x=0 ∧ x.1 1≠0 ∧ x.1 0=0)
    tauto)

def thirdDiagonalEquiv :
    {x : Carrier F // adjoint x=0 ∧ x.1 0=0 ∧ x.1 1=0 ∧ x.1 2≠0} ≃
    {x : Carrier F // adjoint x=0 ∧ x.1 0≠0 ∧ x.1 1=0 ∧ x.1 2=0} :=
  (coordinateCycleEquiv.trans coordinateCycleEquiv).toEquiv.subtypeEquiv (fun x => by
    change (_ ∧ _ ∧ _ ∧ _) ↔
      (adjoint (coordinateCycle (coordinateCycle x))=0 ∧ _ ∧ _ ∧ _)
    rw [cycle_adjoint_zero_iff,cycle_adjoint_zero_iff]
    change (adjoint x=0 ∧ x.1 0=0 ∧ x.1 1=0 ∧ x.1 2≠0) ↔
      (adjoint x=0 ∧ x.1 2≠0 ∧ x.1 0=0 ∧ x.1 1=0)
    tauto)

def whiteSecondDiagonalEquiv :
    {x : Carrier F // adjoint x=0 ∧ x.1 0=0 ∧ x.1 1≠0 ∧ trace x=0} ≃
    {x : Carrier F // adjoint x=0 ∧ x.1 0≠0 ∧ x.1 2=0 ∧ trace x=0} :=
  coordinateCycleEquiv.toEquiv.subtypeEquiv (fun x => by
    change (_ ∧ _ ∧ _ ∧ _) ↔
      (adjoint (coordinateCycle x)=0 ∧ _ ∧ _ ∧ trace (coordinateCycle x)=0)
    rw [cycle_adjoint_zero_iff,cycle_trace]
    change (adjoint x=0 ∧ x.1 0=0 ∧ x.1 1≠0 ∧ trace x=0) ↔
      (adjoint x=0 ∧ x.1 1≠0 ∧ x.1 0=0 ∧ trace x=0)
    tauto)

theorem white_third_diagonal_impossible (x : Carrier F)
    (ha : x.1 0=0) (hb : x.1 1=0) (hc : x.1 2≠0) : trace x≠0 := by
  simpa [trace,ha,hb] using hc

end Atlas.Albert
