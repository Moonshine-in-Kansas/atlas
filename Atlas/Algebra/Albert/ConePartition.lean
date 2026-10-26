import Atlas.Algebra.Albert.DiagonalStrata
import Atlas.LinearAlgebra.PredicateCardSplit

/-! A disjoint coordinate partition of the adjoint-zero cone. -/
namespace Atlas.Albert
variable {F : Type*} [Field F] [Finite F]

theorem card_adjoint_zero_partition :
    Nat.card {x : Carrier F // adjoint x=0} =
      Nat.card {x : Carrier F // adjoint x=0 ∧ x.1 0≠0} +
      Nat.card {x : Carrier F // adjoint x=0 ∧ x.1 0=0 ∧ x.1 1≠0} +
      Nat.card {x : Carrier F // adjoint x=0 ∧ x.1 0=0 ∧ x.1 1=0 ∧ x.1 2≠0} +
      Nat.card {x : Carrier F // x.1=0 ∧ adjoint x=0} := by
  have h1 := Atlas.card_predicate_split (fun x : Carrier F => adjoint x=0)
    (fun x => x.1 0=0)
  have h2 := Atlas.card_predicate_split (fun x : Carrier F => adjoint x=0 ∧ x.1 0=0)
    (fun x => x.1 1=0)
  have h3 := Atlas.card_predicate_split
    (fun x : Carrier F => adjoint x=0 ∧ x.1 0=0 ∧ x.1 1=0) (fun x => x.1 2=0)
  simp only [and_assoc] at h2 h3
  have hz : Nat.card {x : Carrier F // adjoint x=0 ∧ x.1 0=0 ∧ x.1 1=0 ∧ x.1 2=0} =
      Nat.card {x : Carrier F // x.1=0 ∧ adjoint x=0} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun x => by
      simp [funext_iff,Fin.forall_fin_succ,and_comm,and_left_comm,and_assoc] <;> tauto)
  rw [hz] at h3
  simp only [ne_eq] at *
  omega

end Atlas.Albert
