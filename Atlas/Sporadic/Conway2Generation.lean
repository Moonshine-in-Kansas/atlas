import Atlas.Sporadic.Conway2Commutators
import Atlas.Conway.Co2NormalGeneration
import Mathlib.GroupTheory.IsPerfect

noncomputable section
namespace Atlas.Sporadic.Conway2
open Atlas.Conway

def outerPairRestriction := co2PairRestriction
def outerPairSection := co2PairSection

theorem outerPairSection_rightInverse (p : Equiv.Perm Co2MarkedPair) :
    outerPairRestriction (outerPairSection p) = p := co2PairSection_rightInverse p

def embeddedSigns : Subgroup Model := co2Signs

theorem signs_normalClosure : Subgroup.normalClosure (embeddedSigns : Set Model) = ⊤ :=
  co2Signs_normalClosure

theorem commutator_eq_top : commutator Model = ⊤ := co2_commutator_eq_top

theorem perfect : Group.IsPerfect Model := ⟨commutator_eq_top⟩

end Atlas.Sporadic.Conway2
