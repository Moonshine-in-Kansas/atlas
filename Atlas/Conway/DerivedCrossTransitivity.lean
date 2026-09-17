import Atlas.Conway.MinimalVectorOrder
import Atlas.Conway.MonomialCentralQuotient
import Mathlib.GroupTheory.GroupAction.Primitive

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

instance leechCrossAction : MulAction LeechIsometryGroup LeechCross :=
  MulAction.compHom LeechCross crossRepresentation

instance quotientLeechCrossAction : MulAction LeechCentralQuotient LeechCross :=
  MulAction.compHom LeechCross quotientCrossRepresentation

theorem full_cross_stabilizer :
    MulAction.stabilizer LeechIsometryGroup standardCross = monomialSubgroup :=
  standardCrossStabilizer_eq_monomial

set_option maxRecDepth 10000 in
theorem standardCross_orbit_card :
    Nat.card (MulAction.orbit LeechIsometryGroup standardCross) = 8292375 := by
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup LeechIsometryGroup standardCross)
  rw [Nat.card_prod,full_cross_stabilizer,monomial_order,leechIsometryGroup_order] at hc
  apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 1002795171840)
  exact hc.trans (by norm_num)

theorem full_cross_transitive : MulAction.IsPretransitive LeechIsometryGroup LeechCross := by
  have he : MulAction.orbit LeechIsometryGroup standardCross = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    rw [Set.ncard_univ,leechCross_card]
    change 8292375 ≤ Nat.card (MulAction.orbit LeechIsometryGroup standardCross)
    rw [standardCross_orbit_card]
  exact (MulAction.isPretransitive_iff_orbit_eq_univ standardCross).mpr he

theorem quotient_cross_transitive : MulAction.IsPretransitive LeechCentralQuotient LeechCross := by
  letI := full_cross_transitive
  constructor
  intro x y
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq LeechIsometryGroup x y
  exact ⟨leechCentralProjection g,hg⟩

theorem leechCentralQuotient_order :
    Nat.card LeechCentralQuotient = 4157776806543360000 := by
  have hc := leechCentralQuotient_card_relation
  rw [leechIsometryGroup_order] at hc
  omega

theorem quotient_cross_faithful : FaithfulSMul LeechCentralQuotient LeechCross := by
  constructor
  intro g h he
  apply quotientCrossRepresentation_injective
  exact Equiv.ext he

end Atlas.Conway
