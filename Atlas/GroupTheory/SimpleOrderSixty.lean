import Atlas.GroupTheory.SimpleOrderSixtySylow
import Atlas.GroupTheory.SimpleIndexFiveAlternating

/-! # Elementary recognition of a nonabelian simple group of order sixty

The comparison is the coset action of the subgroup of index five constructed
by Sylow counting and a centralizer argument. No classification is used.
-/
noncomputable section
namespace Atlas.GroupTheory

/-- The actual index-five coset action realizes every nonabelian simple group of order sixty as A5. -/
def smallSimpleOrder60EquivAlt5 (G : Type*) [Group G] [Finite G] [IsSimpleGroup G]
    (hcard : Nat.card G = 60) (hnoncomm : ¬IsMulCommutative G) :
    G ≃* alternatingGroup (Fin 5) :=
  simpleOrderSixtyEquivAlt5OfIndexFive hcard
    (Classical.choose (subgroup_index_five_of_simple_card_sixty hcard hnoncomm))
    (Classical.choose_spec (subgroup_index_five_of_simple_card_sixty hcard hnoncomm))

end Atlas.GroupTheory
