import Atlas.LinearGroups.Chevalley.WeightRootCharacterDescent
import Atlas.LinearGroups.Chevalley.LatticeCharacterCounts
import Atlas.LinearGroups.Chevalley.UnimodularCharacterCounts

/-! Cardinalities of the actual adjoint torus parameter kernels.
These are not full companion projection-kernel or group-center formulas. -/
noncomputable section
namespace Atlas.Chevalley
open Classical
local instance torusKernelCountsE6Fintype : Fintype E6Data.Root := Fintype.ofFinite _
variable (K : Type*) [Field K] [Fintype K]

theorem typeA_adjointTorusKernel_card (r : ℕ) :
    Nat.card (adjointTorusParameters (TypeAData.pairing (r+1)) (TypeAData.base r) K).ker =
      Nat.gcd (r+1) (Fintype.card K - 1) := by
  rw [adjointTorusKernel_card]
  exact typeA_weightRootCharacters_card K r

theorem typeB_adjointTorusKernel_card (n : ℕ) :
    Nat.card (adjointTorusParameters (ClassicalData.pairingB (n+1)) (ClassicalData.baseB n) K).ker =
      Nat.gcd 2 (Fintype.card K - 1) := by
  rw [adjointTorusKernel_card]
  exact typeB_weightRootCharacters_card K n

theorem typeC_adjointTorusKernel_card (n : ℕ) :
    Nat.card (adjointTorusParameters (ClassicalData.pairingC (n+1)) (ClassicalData.baseC n) K).ker =
      Nat.gcd 2 (Fintype.card K - 1) := by
  rw [adjointTorusKernel_card]
  exact typeC_weightRootCharacters_card K n

theorem typeD_odd_adjointTorusKernel_card (n : ℕ) (hn : Odd (n+2)) :
    Nat.card (adjointTorusParameters (ClassicalData.pairingD (n+2)) (ClassicalData.baseD n) K).ker =
      Nat.gcd 4 (Fintype.card K - 1) := by
  rw [adjointTorusKernel_card]
  exact typeD_odd_weightRootCharacters_card K n hn

theorem typeD_even_adjointTorusKernel_card (n : ℕ) (hn : Even (n+2)) :
    Nat.card (adjointTorusParameters (ClassicalData.pairingD (n+2)) (ClassicalData.baseD n) K).ker =
      Nat.gcd 2 (Fintype.card K - 1) ^ 2 := by
  rw [adjointTorusKernel_card]
  exact typeD_even_weightRootCharacters_card K n hn

theorem E6_adjointTorusKernel_card :
    Nat.card (adjointTorusParameters E6Data.pairing E6Data.base K).ker =
      Nat.gcd 3 (Fintype.card K - 1) := by
  rw [adjointTorusKernel_card]
  exact E6_weightRootCharacters_card K

theorem E7_adjointTorusKernel_card :
    Nat.card (adjointTorusParameters E7Data.pairing E7Data.base K).ker =
      Nat.gcd 2 (Fintype.card K - 1) := by
  rw [adjointTorusKernel_card]
  exact E7_weightRootCharacters_card K

theorem E8_adjointTorusKernel_card :
    Nat.card (adjointTorusParameters E8Data.pairing E8Data.base K).ker = 1 := by
  rw [adjointTorusKernel_card]
  exact E8_weightRootCharacters_card Kˣ

theorem F4_adjointTorusKernel_card :
    Nat.card (adjointTorusParameters F4Data.pairing F4Data.base K).ker = 1 := by
  rw [adjointTorusKernel_card]
  exact F4_weightRootCharacters_card Kˣ

theorem G2_adjointTorusKernel_card :
    Nat.card (adjointTorusParameters G2Data.pairing G2Data.base K).ker = 1 := by
  rw [adjointTorusKernel_card]
  exact G2_weightRootCharacters_card Kˣ

end Atlas.Chevalley
