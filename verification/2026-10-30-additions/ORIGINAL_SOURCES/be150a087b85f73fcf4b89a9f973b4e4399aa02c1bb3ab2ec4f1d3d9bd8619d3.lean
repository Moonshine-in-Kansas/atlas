import Atlas.Comparisons.Exceptional.G2Binary.Simplicity
import Atlas.LinearGroups.G2.BinaryException
import Atlas.GroupTheory.CommutatorEquiv

namespace Atlas.G2
variable {F : Type*} [Field F] [Finite F]

/-- The actual long-root subgroup is simple in every binary field presentation. -/
theorem longRootNormalClosure_simple_binary (hF : Nat.card F = 2) :
    IsSimpleGroup (longRootNormalClosure (F := F)) := by
  letI := BinaryException.H_simple
  exact (longRootNormalClosureFieldEquiv (binaryFieldEquiv hF)).isSimpleGroup

theorem commutator_eq_longRootNormalClosure_binary (hF : Nat.card F = 2) :
    commutator (Model F) = longRootNormalClosure (F := F) := by
  let e := fieldEquiv (binaryFieldEquiv hF)
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Atlas.GroupTheory.commutator_map_equiv e,
    fieldEquiv_longRootNormalClosure_map (binaryFieldEquiv hF)]
  exact BinaryException.commutator_eq_H

theorem commutator_simple_binary (hF : Nat.card F = 2) :
    IsSimpleGroup (commutator (Model F)) := by
  rw [commutator_eq_longRootNormalClosure_binary hF]
  exact longRootNormalClosure_simple_binary hF

theorem commutator_card_binary (hF : Nat.card F = 2) :
    Nat.card (commutator (Model F)) = 6048 := by
  rw [commutator_eq_longRootNormalClosure_binary hF]
  exact card_longRootNormalClosure_binary hF

theorem commutator_index_binary (hF : Nat.card F = 2) :
    (commutator (Model F)).index = 2 := by
  rw [commutator_eq_longRootNormalClosure_binary hF]
  exact index_longRootNormalClosure_binary hF

theorem commutator_perfect_binary (hF : Nat.card F = 2) :
    Group.IsPerfect (commutator (Model F)) := by
  rw [commutator_eq_longRootNormalClosure_binary hF]
  exact longRootNormalClosure_perfect

theorem commutator_nonabelian_binary (hF : Nat.card F = 2) :
    ¬ IsMulCommutative (commutator (Model F)) := by
  letI := commutator_simple_binary hF
  letI := commutator_perfect_binary hF
  exact Group.IsPerfect.not_isMulCommutative _

end Atlas.G2
