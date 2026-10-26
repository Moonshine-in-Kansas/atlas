import Atlas.LinearGroups.Chevalley.Models
import Atlas.LinearGroups.Chevalley.TorusKernelCounts
import Atlas.Algebra.CenterFactorArithmetic

/-! Match the existing coordinate torus-kernel counts to the existing
uniform root-type center-factor specification. This is not a group-center
or whole-group order theorem. -/
noncomputable section
namespace Atlas.Chevalley
open Classical

/-- The actual torus parameter kernel has the specified center factor for
all validated root types and every finite field. -/
theorem rootDatum_adjointTorusKernel_card (Φ : RootType)
    (K : Type*) [Field K] [Fintype K] :
    Nat.card (adjointTorusParameters (rootDatum Φ).pairing (rootDatum Φ).base K).ker =
      Φ.centerFactor (Fintype.card K) := by
  cases Φ with
  | A r hr => exact typeA_adjointTorusKernel_card K r
  | B r hr => exact typeB_adjointTorusKernel_card K (r - 1)
  | C r hr => exact typeC_adjointTorusKernel_card K (r - 1)
  | D r hr =>
    change Nat.card (adjointTorusParameters (ClassicalData.pairingD (r - 2 + 2))
      (ClassicalData.baseD (r - 2)) K).ker =
        Nat.gcd 4 (Fintype.card K ^ r - 1)
    have hrank : r - 2 + 2 = r := by omega
    have hq : 1 ≤ Fintype.card K := Fintype.card_pos
    rcases Nat.even_or_odd r with he | ho
    · rw [typeD_even_adjointTorusKernel_card K (r - 2) (hrank.symm ▸ he),
        Atlas.gcd_four_pow_sub_one_of_even (Fintype.card K) r hq (by omega) he]
    · rw [typeD_odd_adjointTorusKernel_card K (r - 2) (hrank.symm ▸ ho),
        Atlas.gcd_four_pow_sub_one_of_odd (Fintype.card K) r hq ho]
  | E6 => exact E6_adjointTorusKernel_card K
  | E7 => exact E7_adjointTorusKernel_card K
  | E8 => exact E8_adjointTorusKernel_card K
  | F4 => exact F4_adjointTorusKernel_card K
  | G2 => exact G2_adjointTorusKernel_card K

end Atlas.Chevalley
