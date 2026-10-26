import Atlas.LinearGroups.F4.LongRootSeed
import Atlas.LinearGroups.G2.LongA2Commutator

namespace Atlas.F4
open scoped commutatorElement
variable {F : Type*} [Field F]

theorem longRootSeed_commutator (t : F) :
    ⁅g2Embedding (Atlas.G2.rootB t),g2Embedding (Atlas.G2.rootE 1)⁆ = longRootSeed t := by
  rw [←map_commutatorElement,Atlas.G2.rootB_rootE_commutator,mul_one]
  rfl

theorem longRootSeed_mem_commutator (t : F) : longRootSeed t ∈ commutator (Model F) := by
  rw [←longRootSeed_commutator]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

end Atlas.F4
