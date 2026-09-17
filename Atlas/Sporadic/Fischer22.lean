import Atlas.Fischer.ResidueSimplicity
import Atlas.Fischer.ResidueClasses
import Atlas.Fischer.ResidueCanonical

noncomputable section
namespace Atlas.Sporadic.Fischer22
open Atlas.Fischer Atlas.Codes

/-- The actual centralizer quotient at an arbitrary pair of marked basic involutions. -/
abbrev ModelAt (i j : Omega) := ResidueGroup {i,j}
abbrev Model := ResidueGroup fischer22Marking
abbrev Points := ResiduePoint fischer22Marking
abbrev Centralizer := residueCentralizer fischer22Marking
abbrev CentralKernel := residueCentralElementary fischer22Marking

def projection : Centralizer →* Model := QuotientGroup.mk' CentralKernel
def distinguished : Points → Model := residueDistinguishedElement fischer22Marking

theorem finite : Finite Model := inferInstance
theorem card : Nat.card Model=64561751654400 :=
  residueGroup_pair_order _ fischer22Marking_card
theorem order : Nat.card Model=2^17*3^9*5^2*7*11*13 := by rw [card]; norm_num
theorem simple : IsSimpleGroup Model := residueGroup_simple _ (by simp) (by simp)
theorem noncommutative : ¬IsMulCommutative Model := residueGroup_noncommutative _ (by simp) (by simp)
theorem perfect : Group.IsPerfect Model := residueGroup_perfect _ (by simp) (by simp)
theorem points_card : Nat.card Points=3510 := residuePoint_pair_card _ fischer22Marking_card
theorem faithful : FaithfulSMul Model Points := residueGroup_faithful _ (by simp)
theorem transitive : MulAction.IsPretransitive Model Points := residueGroup_transitive _ (by simp)
theorem primitive : MulAction.IsPreprimitive Model Points := residueGroup_primitive _ (by simp)
theorem distinguished_injective : Function.Injective distinguished := residueDistinguished_injective _ (by simp)
theorem distinguished_order (x : Points) : orderOf (distinguished x)=2 :=
  residueDistinguished_order _ (by simp) x
theorem generated : Subgroup.closure (Set.range distinguished)=⊤ :=
  residueDistinguishedElement_generates _ (by simp)
theorem kernel_card : Nat.card CentralKernel=4 := by
  rw [residueCentralElementary_card _ (by simp),fischer22Marking_card]
  norm_num
theorem projection_surjective : Function.Surjective projection := QuotientGroup.mk'_surjective _
theorem card_at (i j : Omega) (hij : i≠j) : Nat.card (ModelAt i j)=64561751654400 :=
  residueGroup_pair_order _ (by simp [hij])
theorem simple_at (i j : Omega) (hij : i≠j) : IsSimpleGroup (ModelAt i j) :=
  residueGroup_simple _ (by simp) (by simp [hij])

theorem subdegrees (i : Omega) (hi : i ∉ fischer22Marking) (j : Fin 3) :
    Nat.card {x : Points // residueSuborbitIndex fischer22Marking i hi x=j}=![1,693,2816] j := by
  have h := residueSuborbit_card fischer22Marking (by simp) i hi j
  fin_cases j <;> simpa [fischerRankThreeSubdegree,fischer22Marking_card] using h

theorem rank_three (i : Omega) (hi : i ∉ fischer22Marking) :
    Nat.card (MulAction.orbitRel.Quotient
      (MulAction.stabilizer Model (residueBasicPoint fischer22Marking i hi)) Points)=3 :=
  residueGroup_rank_three fischer22Marking (by simp) i hi

structure
 Construction : Prop where
  finite : Finite Model
  card : Nat.card Model=64561751654400
  simple : IsSimpleGroup Model
  noncommutative : ¬IsMulCommutative Model
  points : Nat.card Points=3510
  faithful : FaithfulSMul Model Points
  primitive : MulAction.IsPreprimitive Model Points
  generated : Subgroup.closure (Set.range distinguished)=⊤

theorem construction : Construction :=
  ⟨finite,card,simple,noncommutative,points_card,faithful,primitive,generated⟩

theorem exists_model : ∃ (G : Type) (_ : Group G), Finite G ∧
    Nat.card G=64561751654400 ∧ IsSimpleGroup G ∧ ¬IsMulCommutative G :=
  ⟨Model,inferInstance,finite,card,simple,noncommutative⟩

end Atlas.Sporadic.Fischer22
