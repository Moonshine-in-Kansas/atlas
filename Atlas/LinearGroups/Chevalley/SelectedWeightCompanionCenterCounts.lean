import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionCenterQuotient
import Atlas.LinearGroups.Chevalley.RootDatumTorusKernelCounts

/-! Numerical full-center counts for the actual selected companion models.
Every finite field is included, in particular characteristics two and three.
These are center sizes, not whole-group orders or simplicity statements. -/
noncomputable section
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule

/-- Transfer the proved full-center character identification to the existing
actual torus-kernel count. No good-range hypothesis is needed. -/
theorem selectedWeightCompanion_center_card (Φ : RootType)
    (K : Type*) [Field K] [Fintype K] :
    Nat.card (Subgroup.center (SelectedWeightCompanion Φ K)) =
      Φ.centerFactor (Fintype.card K) := by
  have hc := weightCompanion_center_card_eq_adjointTorusKernel
    (rootDatum Φ).pairing (rootDatum Φ).base (selectedWeightOrbits Φ)
    (selectedWeightOrbits_closed Φ) (selectedWeightOrbits_minuscule Φ) K
    (rootDatum_simpleDiamondProducts Φ) (selectedWeightSet_spans Φ)
  exact hc.trans (rootDatum_adjointTorusKernel_card Φ K)

variable (K : Type*) [Field K] [Fintype K]

theorem selectedWeightCompanion_A_center_card (r : ℕ) (hr : 1 ≤ r) :
    Nat.card (Subgroup.center (SelectedWeightCompanion (.A r hr) K)) =
      Nat.gcd (r + 1) (Fintype.card K - 1) :=
  selectedWeightCompanion_center_card (.A r hr) K

theorem selectedWeightCompanion_B_center_card (r : ℕ) (hr : 2 ≤ r) :
    Nat.card (Subgroup.center (SelectedWeightCompanion (.B r hr) K)) =
      Nat.gcd 2 (Fintype.card K - 1) :=
  selectedWeightCompanion_center_card (.B r hr) K

theorem selectedWeightCompanion_C_center_card (r : ℕ) (hr : 2 ≤ r) :
    Nat.card (Subgroup.center (SelectedWeightCompanion (.C r hr) K)) =
      Nat.gcd 2 (Fintype.card K - 1) :=
  selectedWeightCompanion_center_card (.C r hr) K

theorem selectedWeightCompanion_D_center_card (r : ℕ) (hr : 4 ≤ r) :
    Nat.card (Subgroup.center (SelectedWeightCompanion (.D r hr) K)) =
      Nat.gcd 4 (Fintype.card K ^ r - 1) :=
  selectedWeightCompanion_center_card (.D r hr) K

theorem selectedWeightCompanion_E6_center_card :
    Nat.card (Subgroup.center (SelectedWeightCompanion .E6 K)) =
      Nat.gcd 3 (Fintype.card K - 1) :=
  selectedWeightCompanion_center_card .E6 K

theorem selectedWeightCompanion_E7_center_card :
    Nat.card (Subgroup.center (SelectedWeightCompanion .E7 K)) =
      Nat.gcd 2 (Fintype.card K - 1) :=
  selectedWeightCompanion_center_card .E7 K

theorem selectedWeightCompanion_E8_center_card :
    Nat.card (Subgroup.center (SelectedWeightCompanion .E8 K)) = 1 :=
  selectedWeightCompanion_center_card .E8 K

theorem selectedWeightCompanion_F4_center_card :
    Nat.card (Subgroup.center (SelectedWeightCompanion .F4 K)) = 1 :=
  selectedWeightCompanion_center_card .F4 K

theorem selectedWeightCompanion_G2_center_card :
    Nat.card (Subgroup.center (SelectedWeightCompanion .G2 K)) = 1 :=
  selectedWeightCompanion_center_card .G2 K

end Atlas.Chevalley
