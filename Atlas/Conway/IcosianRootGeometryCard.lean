import Atlas.Conway.IcosianRootPointCount
import Atlas.Lattices.IcosianRootCount

namespace Atlas.Conway
open Atlas.Lattices

theorem icosianRootPoint_card : Nat.card IcosianRootPoint=315 :=
  icosianRootPoint_card_of_root_card icosianRoots_card

instance icosianRootPoint_finite : Finite IcosianRootPoint :=
  Nat.finite_of_card_ne_zero (by rw [icosianRootPoint_card]; decide)

end Atlas.Conway
