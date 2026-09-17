import Atlas.Fischer.FischerPositiveSimplicity
import Atlas.Fischer.PositiveRayAction

noncomputable section
namespace Atlas.Sporadic.Fischer24Prime
open Atlas.Fischer

/-- The actual even-parity subgroup of the algebra-derived ray group. -/
abbrev Model := rootGeneratedRayParity.ker
abbrev Ambient := rootGeneratedRayGroup
abbrev Points := DisplayedReflectingRay

def inclusion : Model →* Ambient := rootGeneratedRayParity.ker.subtype

theorem finite : Finite Model := inferInstance
theorem card : Nat.card Model=1255205709190661721292800 := rootGeneratedRayPositive_order
theorem order : Nat.card Model=2^21*3^16*5^2*7^3*11*13*17*23*29 := by rw [card]; norm_num
theorem simple : IsSimpleGroup Model := rootGeneratedRayPositive_simple
theorem noncommutative : ¬IsMulCommutative Model := rootGeneratedRayPositive_noncommutative
theorem perfect : Group.IsPerfect Model := rootGeneratedRayParity_kernel_perfect
theorem points_card : Nat.card Points=306936 := displayedReflectingRay_card
theorem faithful : FaithfulSMul Model Points := rootGeneratedRayPositive_faithful
theorem transitive : MulAction.IsPretransitive Model Points := rootGeneratedRayPositive_transitive
theorem ambient_primitive : MulAction.IsPreprimitive Ambient Points := rootGeneratedRayGroup_primitive
theorem inclusion_injective : Function.Injective inclusion := Subtype.val_injective
theorem index : rootGeneratedRayParity.ker.index=2 := rootGeneratedRayParity_index
theorem derived : commutator Ambient=rootGeneratedRayParity.ker := rootGeneratedRay_commutator

structure Construction : Prop where
  finite : Finite Model
  card : Nat.card Model=1255205709190661721292800
  simple : IsSimpleGroup Model
  noncommutative : ¬IsMulCommutative Model
  points : Nat.card Points=306936
  faithful : FaithfulSMul Model Points
  transitive : MulAction.IsPretransitive Model Points
  derived : commutator Ambient=rootGeneratedRayParity.ker

theorem construction : Construction :=
  ⟨finite,card,simple,noncommutative,points_card,faithful,transitive,derived⟩

theorem exists_model : ∃ (G : Type) (_ : Group G), Finite G ∧
    Nat.card G=1255205709190661721292800 ∧ IsSimpleGroup G ∧ ¬IsMulCommutative G :=
  ⟨Model,inferInstance,finite,card,simple,noncommutative⟩

end Atlas.Sporadic.Fischer24Prime
