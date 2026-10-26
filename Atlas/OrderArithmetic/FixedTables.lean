import Atlas.OrderArithmetic.FixedTables.M11
import Atlas.OrderArithmetic.FixedTables.M12
import Atlas.OrderArithmetic.FixedTables.M22
import Atlas.OrderArithmetic.FixedTables.M23
import Atlas.OrderArithmetic.FixedTables.M24
import Atlas.OrderArithmetic.FixedTables.J1
import Atlas.OrderArithmetic.FixedTables.J2
import Atlas.OrderArithmetic.FixedTables.J3
import Atlas.OrderArithmetic.FixedTables.J4
import Atlas.OrderArithmetic.FixedTables.HS
import Atlas.OrderArithmetic.FixedTables.McL
import Atlas.OrderArithmetic.FixedTables.He
import Atlas.OrderArithmetic.FixedTables.Ru
import Atlas.OrderArithmetic.FixedTables.Suz
import Atlas.OrderArithmetic.FixedTables.ON
import Atlas.OrderArithmetic.FixedTables.Co3
import Atlas.OrderArithmetic.FixedTables.Co2
import Atlas.OrderArithmetic.FixedTables.Fi22
import Atlas.OrderArithmetic.FixedTables.HN
import Atlas.OrderArithmetic.FixedTables.Ly
import Atlas.OrderArithmetic.FixedTables.Th
import Atlas.OrderArithmetic.FixedTables.Fi23
import Atlas.OrderArithmetic.FixedTables.Co1
import Atlas.OrderArithmetic.FixedTables.Fi24prime
import Atlas.OrderArithmetic.FixedTables.Baby
import Atlas.OrderArithmetic.FixedTables.Monster
import Atlas.OrderArithmetic.FixedTables.Tits

namespace Atlas.OrderArithmetic

theorem fixed_candidates_empty (s : FixedLabel) : orderCandidates (fixedOrder s) = ∅ := by
  cases s
  · exact fixed_candidates_M11
  · exact fixed_candidates_M12
  · exact fixed_candidates_M22
  · exact fixed_candidates_M23
  · exact fixed_candidates_M24
  · exact fixed_candidates_J1
  · exact fixed_candidates_J2
  · exact fixed_candidates_J3
  · exact fixed_candidates_J4
  · exact fixed_candidates_HS
  · exact fixed_candidates_McL
  · exact fixed_candidates_He
  · exact fixed_candidates_Ru
  · exact fixed_candidates_Suz
  · exact fixed_candidates_ON
  · exact fixed_candidates_Co3
  · exact fixed_candidates_Co2
  · exact fixed_candidates_Fi22
  · exact fixed_candidates_HN
  · exact fixed_candidates_Ly
  · exact fixed_candidates_Th
  · exact fixed_candidates_Fi23
  · exact fixed_candidates_Co1
  · exact fixed_candidates_Fi24prime
  · exact fixed_candidates_Baby
  · exact fixed_candidates_Monster
  · exact fixed_candidates_Tits

theorem lie_ne_fixed {x : RawEntry} (hx : Admissible x) (hl : IsLie x)
    (s : FixedLabel) : order x ≠ order (.fixed s) := by
  intro h
  have hm := mem_orderCandidates_of_order_eq hx hl h
  rw [show order (.fixed s) = fixedOrder s from rfl, fixed_candidates_empty] at hm
  exact Finset.notMem_empty x hm

end Atlas.OrderArithmetic
