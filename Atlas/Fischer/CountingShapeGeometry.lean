import Atlas.Fischer.CountingShapeSums
import Atlas.Fischer.CountingColumnIntersections

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def countingSourceBaseOctad : Octad :=
  countingSourceOctadEquiv (.inl ⟨countingTableD,by decide⟩)

theorem countingSourceShape_admissible (t : CountingSourceParameters) :
    OctadPairAdmissible countingSourceBaseOctad (countingSourceOctadEquiv t) ↔
      countingShapeAdmissible (countingSourceShape t) := by
  unfold OctadPairAdmissible countingSourceBaseOctad
  rw [countingSourceA_inter_card]
  simp only [countingColumnProfile, countingPointColumn_source, countingSourceShape_profile]
  rw [countingShape_admissible_profile]
  exact or_comm

theorem countingSourceShape_row_card (trio : Bool) (r : Fin 14) :
    Nat.card {t : CountingSourceParameters //
      OctadPairAdmissible countingSourceBaseOctad (countingSourceOctadEquiv t) ∧
        countingShapeRow trio (countingSourceShape t)=r} =
      countingShapeExpectedMultiplicity trio r := by
  classical
  have he := Equiv.subtypeEquivRight (fun t : CountingSourceParameters =>
    and_congr_left (c := countingShapeRow trio (countingSourceShape t)=r)
      (fun _ => countingSourceShape_admissible t))
  rw [Nat.card_congr he, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  exact countingSourceShape_row_sum trio r

end Atlas.Fischer
