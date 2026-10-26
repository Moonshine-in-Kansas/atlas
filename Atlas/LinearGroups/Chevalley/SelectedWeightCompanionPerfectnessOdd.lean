import Atlas.LinearGroups.Chevalley.SelectedWeightCompanion
import Atlas.LinearGroups.Chevalley.WeightCompanionCrossTorus
import Atlas.LinearGroups.Chevalley.RootData.OddCartanRows
import Mathlib.GroupTheory.OrderOfElement

/-! Actual selected-companion applications. No kernel premise. -/
namespace Atlas.Chevalley
open Group
theorem selectedWeightCompanion_isPerfect_of_odd_cartan_rows
    (Φ : RootType) (K : Type*) [Field K] (hchar : (-1 : K) ≠ 1)
    (hrows : ∀ i : (rootDatum Φ).base.support, ∃ j : (rootDatum Φ).base.support,
      Odd ((rootDatum Φ).base.cartanMatrix i j)) :
    IsPerfect (SelectedWeightCompanion Φ K) :=
  weightCompanion_isPerfect_of_odd_cartan_rows (rootDatum Φ).pairing (rootDatum Φ).base
    (selectedWeightOrbits Φ) (selectedWeightOrbits_closed Φ)
    (selectedWeightOrbits_minuscule Φ) K hchar hrows

variable (K : Type*) [Field K]

theorem selectedWeightCompanion_E6_isPerfect_of_neg_one_ne_one (hchar : (-1 : K) ≠ 1) :
    IsPerfect (SelectedWeightCompanion .E6 K) :=
  selectedWeightCompanion_isPerfect_of_odd_cartan_rows .E6 K hchar E6_base_odd_rows

theorem selectedWeightCompanion_E7_isPerfect_of_neg_one_ne_one (hchar : (-1 : K) ≠ 1) :
    IsPerfect (SelectedWeightCompanion .E7 K) :=
  selectedWeightCompanion_isPerfect_of_odd_cartan_rows .E7 K hchar E7_base_odd_rows

theorem selectedWeightCompanion_E8_isPerfect_of_neg_one_ne_one (hchar : (-1 : K) ≠ 1) :
    IsPerfect (SelectedWeightCompanion .E8 K) :=
  selectedWeightCompanion_isPerfect_of_odd_cartan_rows .E8 K hchar E8_base_odd_rows

theorem selectedWeightCompanion_F4_isPerfect_of_neg_one_ne_one (hchar : (-1 : K) ≠ 1) :
    IsPerfect (SelectedWeightCompanion .F4 K) :=
  selectedWeightCompanion_isPerfect_of_odd_cartan_rows .F4 K hchar F4_base_odd_rows

theorem selectedWeightCompanion_G2_isPerfect_of_neg_one_ne_one (hchar : (-1 : K) ≠ 1) :
    IsPerfect (SelectedWeightCompanion .G2 K) :=
  selectedWeightCompanion_isPerfect_of_odd_cartan_rows .G2 K hchar G2_base_odd_rows

theorem selectedWeightCompanion_A_isPerfect_of_neg_one_ne_one (r : ℕ) (hr : 2 ≤ r)
    (hchar : (-1 : K) ≠ 1) : IsPerfect (SelectedWeightCompanion (.A r (by omega)) K) := by
  apply selectedWeightCompanion_isPerfect_of_odd_cartan_rows (.A r (by omega)) K hchar
  with_unfolding_all exact A_base_odd_rows r hr

theorem selectedWeightCompanion_B_isPerfect_of_neg_one_ne_one (r : ℕ) (hr : 3 ≤ r)
    (hchar : (-1 : K) ≠ 1) : IsPerfect (SelectedWeightCompanion (.B r (by omega)) K) := by
  apply selectedWeightCompanion_isPerfect_of_odd_cartan_rows (.B r (by omega)) K hchar
  with_unfolding_all exact B_base_odd_rows (r-1) (by omega)

theorem selectedWeightCompanion_D_isPerfect_of_neg_one_ne_one (r : ℕ) (hr : 4 ≤ r)
    (hchar : (-1 : K) ≠ 1) : IsPerfect (SelectedWeightCompanion (.D r (by omega)) K) := by
  apply selectedWeightCompanion_isPerfect_of_odd_cartan_rows (.D r (by omega)) K hchar
  with_unfolding_all exact D_base_odd_rows (r-2) (by omega)

end Atlas.Chevalley

namespace Atlas.Chevalley
open Group
variable (K : Type*) [Field K] [Fintype K]


theorem selectedWeightCompanion_E6_isPerfect_of_card_three (hq : Fintype.card K = 3) :
    IsPerfect (SelectedWeightCompanion .E6 K) :=
  selectedWeightCompanion_E6_isPerfect_of_neg_one_ne_one K (neg_one_ne_one_of_card_three K hq)

theorem selectedWeightCompanion_E7_isPerfect_of_card_three (hq : Fintype.card K = 3) :
    IsPerfect (SelectedWeightCompanion .E7 K) :=
  selectedWeightCompanion_E7_isPerfect_of_neg_one_ne_one K (neg_one_ne_one_of_card_three K hq)

theorem selectedWeightCompanion_E8_isPerfect_of_card_three (hq : Fintype.card K = 3) :
    IsPerfect (SelectedWeightCompanion .E8 K) :=
  selectedWeightCompanion_E8_isPerfect_of_neg_one_ne_one K (neg_one_ne_one_of_card_three K hq)

theorem selectedWeightCompanion_F4_isPerfect_of_card_three (hq : Fintype.card K = 3) :
    IsPerfect (SelectedWeightCompanion .F4 K) :=
  selectedWeightCompanion_F4_isPerfect_of_neg_one_ne_one K (neg_one_ne_one_of_card_three K hq)

theorem selectedWeightCompanion_G2_isPerfect_of_card_three (hq : Fintype.card K = 3) :
    IsPerfect (SelectedWeightCompanion .G2 K) :=
  selectedWeightCompanion_G2_isPerfect_of_neg_one_ne_one K (neg_one_ne_one_of_card_three K hq)

theorem selectedWeightCompanion_A_isPerfect_of_card_three (r : ℕ) (hr : 2 ≤ r)
    (hq : Fintype.card K = 3) : IsPerfect (SelectedWeightCompanion (.A r (by omega)) K) :=
  selectedWeightCompanion_A_isPerfect_of_neg_one_ne_one K r hr (neg_one_ne_one_of_card_three K hq)

theorem selectedWeightCompanion_B_isPerfect_of_card_three (r : ℕ) (hr : 3 ≤ r)
    (hq : Fintype.card K = 3) : IsPerfect (SelectedWeightCompanion (.B r (by omega)) K) :=
  selectedWeightCompanion_B_isPerfect_of_neg_one_ne_one K r hr (neg_one_ne_one_of_card_three K hq)

theorem selectedWeightCompanion_D_isPerfect_of_card_three (r : ℕ) (hr : 4 ≤ r)
    (hq : Fintype.card K = 3) : IsPerfect (SelectedWeightCompanion (.D r (by omega)) K) :=
  selectedWeightCompanion_D_isPerfect_of_neg_one_ne_one K r hr (neg_one_ne_one_of_card_three K hq)

end Atlas.Chevalley
