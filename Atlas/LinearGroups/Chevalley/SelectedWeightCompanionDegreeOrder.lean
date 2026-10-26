import Atlas.LinearGroups.Chevalley.ModelAOrder
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionBCOrder
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionDOrder
import Atlas.LinearGroups.Chevalley.ModelE6Order
import Atlas.LinearGroups.Chevalley.ModelE7Order
import Atlas.LinearGroups.Chevalley.ModelE8Order
import Atlas.LinearGroups.Chevalley.ModelF4Order
import Atlas.LinearGroups.Chevalley.ModelG2Order

/-! The uniform degree-list formula for the actual selected linear companion.
The list retains multiplicity. Its proof uses the independently proved orders
of the nine actual root-operator constructions, without a simplicity hypothesis.
This source candidate awaits the final E8 factor and separate dependency audit. -/
noncomputable section
namespace Atlas.Chevalley

private theorem prod_map_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.prod_range_succ, ih]

theorem selectedWeightCompanion_card_eq_orderPolynomial
    (Φ : RootType) (K : Type*) [Field K] [Finite K] :
    Nat.card (SelectedWeightCompanion Φ K) = Φ.orderPolynomial (Nat.card K) := by
  cases Φ with
  | A r hr =>
    simpa only [RootType.orderPolynomial, RootType.positiveRootNumber,
      RootType.degrees, List.map_map, Function.comp_def, prod_map_range]
      using selectedWeightCompanion_A_card r hr K
  | B r hr =>
    simpa only [RootType.orderPolynomial, RootType.positiveRootNumber,
      RootType.degrees, List.map_map, Function.comp_def, prod_map_range]
      using selectedWeightCompanion_B_card r hr K
  | C r hr =>
    simpa only [RootType.orderPolynomial, RootType.positiveRootNumber,
      RootType.degrees, List.map_map, Function.comp_def, prod_map_range]
      using selectedWeightCompanion_C_card r hr K
  | D r hr =>
    rw [selectedWeightCompanion_D_card]
    simp only [RootType.orderPolynomial, RootType.positiveRootNumber,
      RootType.degrees, List.map_append, List.map_map, Function.comp_def,
      List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, prod_map_range]
    ac_rfl
  | E6 =>
    simpa only [RootType.orderPolynomial, RootType.positiveRootNumber,
      RootType.degrees, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using selectedWeightCompanion_E6_card K
  | E7 =>
    simpa only [RootType.orderPolynomial, RootType.positiveRootNumber,
      RootType.degrees, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using selectedWeightCompanion_E7_card K
  | E8 =>
    simpa only [RootType.orderPolynomial, RootType.positiveRootNumber,
      RootType.degrees, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using selectedWeightCompanion_E8_card K
  | F4 =>
    simpa only [RootType.orderPolynomial, RootType.positiveRootNumber,
      RootType.degrees, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using selectedWeightCompanion_F4_card K
  | G2 =>
    simpa only [RootType.orderPolynomial, RootType.positiveRootNumber,
      RootType.degrees, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, one_mul, mul_assoc, mul_comm, mul_left_comm]
      using selectedWeightCompanion_G2_card K

end Atlas.Chevalley
