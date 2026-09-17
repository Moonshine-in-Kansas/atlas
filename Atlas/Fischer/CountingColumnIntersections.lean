import Atlas.Fischer.CountingPointColumns

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

def countingColumnProfile (G : Finset Omega) : CountingColumnVector :=
  fun i => (countingPointColumn G i).card

def countingColumnJointProfile (G H : Finset Omega) : CountingColumnVector :=
  fun i => (countingPointColumn G i ∩ countingPointColumn H i).card

theorem countingColumnJointProfile_sum (G H : Finset Omega) :
    (∑ i : Fin 6, countingColumnJointProfile G H i)=(G ∩ H).card := by
  simp only [countingColumnJointProfile,← countingPointColumn_inter]
  exact countingPointColumn_card_sum (G ∩ H)

theorem countingSourceA_inter_card (t : CountingSourceTypeA) (G : Finset Omega) :
    ((countingSourceOctadEquiv (.inl t)).val ∩ G).card=
      ∑ i ∈ t.val, countingColumnProfile G i := by
  rw [← countingPointColumn_card_sum]
  simp only [countingPointColumn_inter,countingPointColumn_source,countingSourceColumn]
  have he (i : Fin 6) : ((if i ∈ t.val then Finset.univ else ∅) ∩ countingPointColumn G i).card=
      if i ∈ t.val then countingColumnProfile G i else 0 := by
    by_cases hi : i ∈ t.val <;> simp [hi,countingColumnProfile]
  simp_rw [he]
  simp

theorem countingSourceA_triple_inter_card (t : CountingSourceTypeA) (G H : Finset Omega) :
    (((countingSourceOctadEquiv (.inl t)).val ∩ G) ∩ H).card=
      ∑ i ∈ t.val, countingColumnJointProfile G H i := by
  rw [Finset.inter_assoc,countingSourceA_inter_card]
  simp only [countingColumnProfile,countingColumnJointProfile,countingPointColumn_inter]

end Atlas.Fischer
