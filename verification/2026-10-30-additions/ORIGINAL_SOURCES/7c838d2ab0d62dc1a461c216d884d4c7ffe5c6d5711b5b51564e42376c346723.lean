import Atlas.Comparisons.Exceptional.G2Binary.FieldNine
import Atlas.LinearGroups.Unitary.ProjectiveOrder

/-!
ISO-6048 final bridge, 27 October 2026. SOURCE ONLY; UNCOMPILED AND UNAUDITED.

Independent order specialization for the exact quadratic-algebra presentation
used by Source6048.Projective. This module deliberately has no dependency on
the marked action, matching words, comparison homomorphism or binary group.
The quotient is the retained quotient by the actual full center.

Parent staging target: ComparisonWork.FieldNineOrder.
-/
noncomputable section
namespace Atlas.Comparisons.G2Binary.Final6048
open Atlas.Unitary

/-- The uniform order formula on the actual marked FieldNine PSU carrier.
Here q = 3, the extension degree is two, and the full-center divisor is
gcd(3, 3 + 1) = 1. This is independent of the proposed comparison map. -/
theorem card_fieldNine_psu :
    Nat.card (PSU BaseThree FieldNine 3 fieldNine_degree) = 6048 := by
  rw [card_psu fieldNine_degree 3 (by decide)]
  norm_num [BaseThree, orderSU, orderFactor, Finset.prod_range_succ, Nat.card_zmod]

end Atlas.Comparisons.G2Binary.Final6048
