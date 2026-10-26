import Atlas.OrderArithmetic.FiniteTables

namespace Atlas.OrderArithmetic

-- A complete table evaluated from a certified prime factorization.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem fixed_candidates_Monster : orderCandidates (fixedOrder .Monster) = ∅ := by
  rw [orderCandidates_eq_from_factors (L := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 7, 7, 7, 7, 7, 7, 11, 11, 13, 13, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71])
    (by norm_num [fixedOrder]) (by decide +kernel)]
  decide +kernel

end Atlas.OrderArithmetic
