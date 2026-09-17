import Atlas.Conway.QuotientGolaySigns
import Atlas.GroupTheory.IwasawaStabilizer

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

theorem leechCentralQuotient_noncommuting_pair :
    ∃ g h : LeechCentralQuotient, g*h ≠ h*g := by
  obtain ⟨g,h,hgh⟩ := mathieu24_noncommuting_pair
  refine ⟨quotientPermutationEmbedding g,quotientPermutationEmbedding h,?_⟩
  intro he
  apply hgh
  apply quotientPermutationEmbedding_injective
  simpa only [map_mul] using he

theorem leechCentralQuotient_simple : IsSimpleGroup LeechCentralQuotient := by
  letI := quotient_cross_faithful
  letI := quotient_cross_primitive
  letI := leechCentralQuotient_perfect
  letI := mathieu24_simple
  letI : Nontrivial LeechCentralQuotient :=
    Function.Injective.nontrivial quotientPermutationEmbedding_injective
  apply Atlas.GroupTheory.iwasawa_stabilizer_simple standardCross quotientGolaySignSubgroup
  · rw [quotient_cross_stabilizer]
    exact quotientGolaySignSubgroup_le_monomial
  · rw [quotient_cross_stabilizer]
    exact quotientGolaySignSubgroup_normal
  · exact quotientGolaySignSubgroup_abelian
  · exact quotientGolaySigns_normalClosure_eq_full

theorem leechCentralQuotient_normal_subgroups (L : Subgroup LeechCentralQuotient) [hL : L.Normal] :
    L = ⊥ ∨ L = ⊤ := by
  letI := leechCentralQuotient_simple
  exact hL.eq_bot_or_eq_top

theorem leechCentralQuotient_center : Subgroup.center LeechCentralQuotient = ⊥ := by
  rcases leechCentralQuotient_normal_subgroups (Subgroup.center LeechCentralQuotient) with he | he
  · exact he
  · have hc := (Subgroup.center_eq_top_iff).mp he
    letI := hc
    obtain ⟨g,h,hgh⟩ := leechCentralQuotient_noncommuting_pair
    exact (hgh (mul_comm' g h)).elim

theorem leechIsometryGroup_not_simple : ¬ IsSimpleGroup LeechIsometryGroup := by
  intro hG
  letI := hG
  rcases (inferInstance : leechCentralSigns.Normal).eq_bot_or_eq_top with he | he
  · have hc := leechCentralSigns_card
    rw [he,Subgroup.card_bot] at hc
    omega
  · have hc := leechCentralSigns_card
    rw [he,Subgroup.card_top,leechIsometryGroup_order] at hc
    omega

end Atlas.Conway
