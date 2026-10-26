import Atlas.LinearGroups.Chevalley.AdjointOddCartan
import Atlas.LinearGroups.Chevalley.RootData.OddCartanRows
import Mathlib.GroupTheory.OrderOfElement

/-! actual model applications. -/
namespace Atlas.Chevalley
open Group
variable (K : Type*) [Field K]

theorem model_E6_isPerfect_of_neg_one_ne_one (hchar : (-1 : K) ≠ 1) :
    IsPerfect (Model .E6 K) :=
  adjoint_isPerfect_of_odd_cartan_rows
    (rootDatum .E6).pairing (rootDatum .E6).base K hchar E6_base_odd_rows

theorem model_E7_isPerfect_of_neg_one_ne_one (hchar : (-1 : K) ≠ 1) :
    IsPerfect (Model .E7 K) :=
  adjoint_isPerfect_of_odd_cartan_rows
    (rootDatum .E7).pairing (rootDatum .E7).base K hchar E7_base_odd_rows

theorem model_E8_isPerfect_of_neg_one_ne_one (hchar : (-1 : K) ≠ 1) :
    IsPerfect (Model .E8 K) :=
  adjoint_isPerfect_of_odd_cartan_rows
    (rootDatum .E8).pairing (rootDatum .E8).base K hchar E8_base_odd_rows

theorem model_F4_isPerfect_of_neg_one_ne_one (hchar : (-1 : K) ≠ 1) :
    IsPerfect (Model .F4 K) :=
  adjoint_isPerfect_of_odd_cartan_rows
    (rootDatum .F4).pairing (rootDatum .F4).base K hchar F4_base_odd_rows

theorem model_G2_isPerfect_of_neg_one_ne_one (hchar : (-1 : K) ≠ 1) :
    IsPerfect (Model .G2 K) :=
  adjoint_isPerfect_of_odd_cartan_rows
    (rootDatum .G2).pairing (rootDatum .G2).base K hchar G2_base_odd_rows

theorem model_A_isPerfect_of_neg_one_ne_one (r : ℕ) (hr : 2 ≤ r)
    (hchar : (-1 : K) ≠ 1) : IsPerfect (Model (.A r (by omega)) K) := by
  apply adjoint_isPerfect_of_odd_cartan_rows
    (rootDatum (.A r (by omega))).pairing (rootDatum (.A r (by omega))).base
    K hchar
  with_unfolding_all exact A_base_odd_rows r hr

theorem model_B_isPerfect_of_neg_one_ne_one (r : ℕ) (hr : 3 ≤ r)
    (hchar : (-1 : K) ≠ 1) : IsPerfect (Model (.B r (by omega)) K) := by
  apply adjoint_isPerfect_of_odd_cartan_rows
    (rootDatum (.B r (by omega))).pairing (rootDatum (.B r (by omega))).base
    K hchar
  with_unfolding_all exact B_base_odd_rows (r-1) (by omega)

theorem model_D_isPerfect_of_neg_one_ne_one (r : ℕ) (hr : 4 ≤ r)
    (hchar : (-1 : K) ≠ 1) : IsPerfect (Model (.D r (by omega)) K) := by
  apply adjoint_isPerfect_of_odd_cartan_rows
    (rootDatum (.D r (by omega))).pairing (rootDatum (.D r (by omega))).base
    K hchar
  with_unfolding_all exact D_base_odd_rows (r-2) (by omega)

end Atlas.Chevalley

namespace Atlas.Chevalley
open Group
variable (K : Type*) [Field K] [Fintype K]

/-- Additive cardinal annihilation proves characteristic is not two here.
This is derived from cardinality, not supplied as an extra assumption. -/
theorem neg_one_ne_one_of_card_three (hq : Fintype.card K = 3) : (-1 : K) ≠ 1 := by
  intro h
  have h3 : (3 : K) = 0 := by simpa only [hq, Nat.cast_ofNat] using Nat.cast_card_eq_zero K
  have h10 : (1 : K) = 0 := by linear_combination h3 + h
  exact one_ne_zero h10

theorem model_E6_isPerfect_of_card_three (hq : Fintype.card K = 3) :
    IsPerfect (Model .E6 K) :=
  model_E6_isPerfect_of_neg_one_ne_one K (neg_one_ne_one_of_card_three K hq)

theorem model_E7_isPerfect_of_card_three (hq : Fintype.card K = 3) :
    IsPerfect (Model .E7 K) :=
  model_E7_isPerfect_of_neg_one_ne_one K (neg_one_ne_one_of_card_three K hq)

theorem model_E8_isPerfect_of_card_three (hq : Fintype.card K = 3) :
    IsPerfect (Model .E8 K) :=
  model_E8_isPerfect_of_neg_one_ne_one K (neg_one_ne_one_of_card_three K hq)

theorem model_F4_isPerfect_of_card_three (hq : Fintype.card K = 3) :
    IsPerfect (Model .F4 K) :=
  model_F4_isPerfect_of_neg_one_ne_one K (neg_one_ne_one_of_card_three K hq)

theorem model_G2_isPerfect_of_card_three (hq : Fintype.card K = 3) :
    IsPerfect (Model .G2 K) :=
  model_G2_isPerfect_of_neg_one_ne_one K (neg_one_ne_one_of_card_three K hq)

theorem model_A_isPerfect_of_card_three (r : ℕ) (hr : 2 ≤ r)
    (hq : Fintype.card K = 3) : IsPerfect (Model (.A r (by omega)) K) :=
  model_A_isPerfect_of_neg_one_ne_one K r hr (neg_one_ne_one_of_card_three K hq)

theorem model_B_isPerfect_of_card_three (r : ℕ) (hr : 3 ≤ r)
    (hq : Fintype.card K = 3) : IsPerfect (Model (.B r (by omega)) K) :=
  model_B_isPerfect_of_neg_one_ne_one K r hr (neg_one_ne_one_of_card_three K hq)

theorem model_D_isPerfect_of_card_three (r : ℕ) (hr : 4 ≤ r)
    (hq : Fintype.card K = 3) : IsPerfect (Model (.D r (by omega)) K) :=
  model_D_isPerfect_of_neg_one_ne_one K r hr (neg_one_ne_one_of_card_three K hq)

end Atlas.Chevalley
