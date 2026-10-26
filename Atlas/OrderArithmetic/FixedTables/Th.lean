import Atlas.OrderArithmetic.FiniteTables

namespace Atlas.OrderArithmetic

-- A complete table evaluated from a certified prime factorization.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem fixed_candidates_Th : orderCandidates (fixedOrder .Th) = ∅ := by
  rw [orderCandidates_eq_from_factors (L := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 7, 7, 13, 19, 31])
    (by norm_num [fixedOrder]) (by decide +kernel)]
  decide +kernel

end Atlas.OrderArithmetic
