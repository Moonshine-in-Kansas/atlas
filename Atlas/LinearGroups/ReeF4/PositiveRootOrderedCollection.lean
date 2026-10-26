import Atlas.LinearGroups.ReeF4.PositiveRootCollects0
import Atlas.LinearGroups.ReeF4.PositiveRootCollects1
import Atlas.LinearGroups.ReeF4.PositiveRootCollects2
import Atlas.LinearGroups.ReeF4.PositiveRootCollects3
import Atlas.LinearGroups.ReeF4.PositiveRootCollects4
import Atlas.LinearGroups.ReeF4.PositiveRootCollects5
import Atlas.LinearGroups.ReeF4.PositiveRootCollects6
import Atlas.LinearGroups.ReeF4.PositiveRootCollects7
noncomputable section
namespace Atlas.ReeF4
open Atlas.GroupTheory
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem positiveRoot_hasOrderedCollection {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    HasOrderedCollection (positiveRootFactorList hcard) :=
  ⟨positiveRoot_collects_0 hcard,⟨positiveRoot_collects_1 hcard,⟨positiveRoot_collects_2 hcard,⟨positiveRoot_collects_3 hcard,⟨positiveRoot_collects_4 hcard,⟨positiveRoot_collects_5 hcard,⟨positiveRoot_collects_6 hcard,⟨positiveRoot_collects_7 hcard,True.intro⟩⟩⟩⟩⟩⟩⟩⟩
end Atlas.ReeF4
