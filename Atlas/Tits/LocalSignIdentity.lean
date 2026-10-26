import Atlas.Tits.LocalOrderThree

namespace Atlas.Tits
open Atlas.Rudvalis Atlas.Codes.Quaternary
open scoped commutatorElement
set_option maxRecDepth 16384

set_option maxHeartbeats 4000000 in
/-- Exact sign-direction identity for the inherited monomial operators. -/
theorem original_double_commutator_sign :
    ⁅⁅coupleOriginalD ^ 4, seedVMonomial⁆, seedVMonomial⁆ =
      seedUnitMonomial 4 ^ 2 * seedOriginalRowSign (binaryLabel 4) := by
  ext z
  all_goals decide +kernel +revert

set_option maxHeartbeats 4000000 in
theorem code_double_commutator_sign :
    ⁅⁅coupleCodeD ^ 4, codeV⁆, codeV⁆ = codeI ^ 2 * seedARowSign (binaryLabel 4) := by
  apply Subtype.ext
  change ⁅⁅coupleCodeD.val ^ 4, codeV.val⁆, codeV.val⁆ =
    codeI.val ^ 2 * (seedARowSign (binaryLabel 4)).val
  rw [coupleCodeD_transport, codeV_transport, seedARowSign_conjugate,
    ← map_pow, ← map_commutatorElement, ← map_commutatorElement,
    original_double_commutator_sign, map_mul, map_pow]
  rfl

end Atlas.Tits
