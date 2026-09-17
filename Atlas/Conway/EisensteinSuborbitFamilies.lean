import Atlas.Conway.EisensteinNineHexadFamily
import Atlas.Conway.EisensteinBalancedNineFamilyCount
import Atlas.Conway.EisensteinUnitFrameCount
import Atlas.Conway.EisensteinSubdegreeArithmetic

set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Lattices
open scoped BigOperators

/-- The thirteen concrete lattice-frame families. This definition and their
cardinalities do not by themselves assert disjointness or exhaustion. -/
def eisensteinSuborbitFrames : Fin 13 → Set EisensteinFrame :=
  ![{eisensteinStandardFrame}, (eisensteinTriadFamily : Set EisensteinFrame),
    (eisensteinHexadFamily : Set EisensteinFrame),
    (eisensteinNineHexadFamily 1 (by decide) : Set EisensteinFrame),
    (eisensteinNineHexadFamily 2 (by decide) : Set EisensteinFrame),
    eisensteinHeavyUnitFrames, eisensteinPairUnitFrames false, eisensteinPairUnitFrames true,
    (eisensteinBalancedFamily : Set EisensteinFrame),
    eisensteinTriadUnitFrames 0, eisensteinTriadUnitFrames 1, eisensteinTriadUnitFrames 2,
    (eisensteinBalancedNineFamily : Set EisensteinFrame)]

def eisensteinSuborbitFinset (i : Fin 13) : Finset EisensteinFrame :=
  (eisensteinSuborbitFrames i).toFinite.toFinset

theorem eisensteinSuborbitFinset_mem (i : Fin 13) (F : EisensteinFrame) :
    F ∈ eisensteinSuborbitFinset i ↔ F ∈ eisensteinSuborbitFrames i :=
  Set.Finite.mem_toFinset _

theorem eisensteinSuborbitFrames_card (i : Fin 13) :
    Nat.card (eisensteinSuborbitFrames i) = eisensteinSubdegree i := by
  fin_cases i
  · change Nat.card ({eisensteinStandardFrame} : Set EisensteinFrame)=1
    simp
  · exact (Nat.card_eq_finsetCard _).trans eisensteinTriadFamily_card
  · exact (Nat.card_eq_finsetCard _).trans eisensteinHexadFamily_card
  · exact (Nat.card_eq_finsetCard _).trans (eisensteinNineHexadFamily_card 1 (by decide))
  · exact (Nat.card_eq_finsetCard _).trans (eisensteinNineHexadFamily_card 2 (by decide))
  · exact eisensteinHeavyUnitFrames_card
  · exact eisensteinPairUnitFrames_card false
  · exact eisensteinPairUnitFrames_card true
  · exact (Nat.card_eq_finsetCard _).trans eisensteinBalancedFamily_card
  · exact eisensteinTriadUnitFrames_card 0
  · exact eisensteinTriadUnitFrames_card 1
  · exact eisensteinTriadUnitFrames_card 2
  · exact (Nat.card_eq_finsetCard _).trans eisensteinBalancedNineFamily_card

theorem eisensteinSuborbitFinset_card (i : Fin 13) :
    (eisensteinSuborbitFinset i).card = eisensteinSubdegree i := by
  rw [eisensteinSuborbitFinset,← Set.ncard_eq_toFinset_card]
  exact eisensteinSuborbitFrames_card i

theorem eisensteinSuborbitFinset_sum :
    (∑ i : Fin 13, (eisensteinSuborbitFinset i).card) = 232960 := by
  simp_rw [eisensteinSuborbitFinset_card]
  exact eisensteinSubdegree_sum

end Atlas.Conway
