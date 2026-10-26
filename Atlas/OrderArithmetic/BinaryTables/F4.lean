import Atlas.OrderArithmetic.BinaryCandidates

namespace Atlas.OrderArithmetic

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
-- Complete finite comparison at one exponent, with ordinary kernel reduction.
theorem binary_table_f4 : ∀ x ∈ binaryClassicalAt 4, ∀ y ∈ binaryClassicalBox,
    order x = order y → BinaryCollision x y := by
  decide +kernel

end Atlas.OrderArithmetic
