import Atlas.Fischer.ResidueSimplicity
import Atlas.Fischer.ResidueClasses
import Atlas.Fischer.ResidueCanonical

noncomputable section
namespace Atlas.Sporadic.Fischer23
open Atlas.Fischer Atlas.Codes

/-- The actual centralizer quotient at an arbitrary marked basic involution. -/
abbrev ModelAt (i : Omega) := ResidueGroup {i}
abbrev Model := ResidueGroup fischer23Marking
abbrev Points := ResiduePoint fischer23Marking
abbrev Centralizer := residueCentralizer fischer23Marking
abbrev CentralKernel := residueCentralElementary fischer23Marking

def projection : Centralizer →* Model := QuotientGroup.mk' CentralKernel
def distinguished : Points → Model := residueDistinguishedElement fischer23Marking

theorem finite : Finite Model := inferInstance
theorem card : Nat.card Model=4089470473293004800 :=
  residueGroup_singleton_order _ fischer23Marking_card
theorem order : Nat.card Model=2^18*3^13*5^2*7*11*13*17*23 := by rw [card]; norm_num
theorem simple : IsSimpleGroup Model := residueGroup_simple _ (by simp) (by simp)
theorem noncommutative : ¬IsMulCommutative Model := residueGroup_noncommutative _ (by simp) (by simp)
theorem perfect : Group.IsPerfect Model := residueGroup_perfect _ (by simp) (by simp)
theorem points_card : Nat.card Points=31671 := residuePoint_singleton_card _ fischer23Marking_card
theorem faithful : FaithfulSMul Model Points := residueGroup_faithful _ (by simp)
theorem transitive : MulAction.IsPretransitive Model Points := residueGroup_transitive _ (by simp)
theorem primitive : MulAction.IsPreprimitive Model Points := residueGroup_primitive _ (by simp)
theorem distinguished_injective : Function.Injective distinguished := residueDistinguished_injective _ (by simp)
theorem distinguished_order (x : Points) : orderOf (distinguished x)=2 :=
  residueDistinguished_order _ (by simp) x
theorem generated : Subgroup.closure (Set.range distinguished)=⊤ :=
  residueDistinguishedElement_generates _ (by simp)
theorem kernel_card : Nat.card CentralKernel=2 := by
  rw [residueCentralElementary_card _ (by simp),fischer23Marking_card]
  norm_num
theorem projection_surjective : Function.Surjective projection := QuotientGroup.mk'_surjective _
theorem card_at (i : Omega) : Nat.card (ModelAt i)=4089470473293004800 :=
  residueGroup_singleton_order _ (Finset.card_singleton i)
theorem simple_at (i : Omega) : IsSimpleGroup (ModelAt i) :=
  residueGroup_simple _ (by simp) (by simp)

theorem subdegrees (i : Omega) (hi : i ∉ fischer23Marking) (j : Fin 3) :
    Nat.card {x : Points // residueSuborbitIndex fischer23Marking i hi x=j}=![1,3510,28160] j := by
  have h := residueSuborbit_card fischer23Marking (by simp) i hi j
  fin_cases j <;> simpa [fischerRankThreeSubdegree,fischer23Marking_card] using h

theorem rank_three (i : Omega) (hi : i ∉ fischer23Marking) :
    Nat.card (MulAction.orbitRel.Quotient
      (MulAction.stabilizer Model (residueBasicPoint fischer23Marking i hi)) Points)=3 :=
  residueGroup_rank_three fischer23Marking (by simp) i hi

structure Construction : Prop where
  finite : Finite Model
  card : Nat.card Model=4089470473293004800
  simple : IsSimpleGroup Model
  noncommutative : ¬IsMulCommutative Model
  points : Nat.card Points=31671
  faithful : FaithfulSMul Model Points
  primitive : MulAction.IsPreprimitive Model Points
  generated : Subgroup.closure (Set.range distinguished)=⊤

theorem construction : Construction :=
  ⟨finite,card,simple,noncommutative,points_card,faithful,primitive,generated⟩

theorem exists_model : ∃ (G : Type) (_ : Group G), Finite G ∧
    Nat.card G=4089470473293004800 ∧ IsSimpleGroup G ∧ ¬IsMulCommutative G :=
  ⟨Model,inferInstance,finite,card,simple,noncommutative⟩

end Atlas.Sporadic.Fischer23
