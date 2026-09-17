import Atlas.Fischer.OctadDuadFibres
import Atlas.Fischer.SignedOctadCrossingProducts
import Atlas.Fischer.OctadShortenedDivisibility

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Differences of two octads with the same restriction lie in the actual shortened code. -/
def octadFibreDifference (O : Octad) (S : Finset Omega) (D E : OctadDuadFibre O S) :
    octadShortenedCode O :=
  ⟨octadWord D.val-octadWord E.val,by
    rw [← octadEvenRestriction_kernel]
    change octadEvenRestriction O (octadWord D.val-octadWord E.val)=0
    rw [map_sub]
    apply sub_eq_zero.mpr
    apply octadEvenRestriction_eq_of_support
    rw [octadWord_support,octadWord_support,D.property,E.property]⟩

/-- Distinct actual octads over the same duad meet in exactly four points. -/
theorem octadDuadFibre_intersection_four (O : Octad) (S : Finset Omega)
    (D E : OctadDuadFibre O S) (hS : S.card=2) (hne : D ≠ E) :
    (D.val.val ∩ E.val.val).card=4 := by
  have hw := octadShortened_weights O (octadFibreDifference O S D E)
  have he : (octadFibreDifference O S D E).val.val=
      (octadWord D.val).val+(octadWord E.val).val := by
    funext i
    change (octadWord D.val).val i-(octadWord E.val).val i =
      (octadWord D.val).val i+(octadWord E.val).val i
    rw [sub_eq_add_neg,CharTwo.neg_eq]
  rw [he] at hw
  have ha := binary_weight_add (octadWord D.val).val (octadWord E.val).val
  rw [octadWord_weight,octadWord_weight,overlap_inter,octadWord_support,octadWord_support] at ha
  have hs : S ⊆ D.val.val ∩ E.val.val := by
    apply Finset.subset_inter
    · intro i hi
      have hm : i ∈ D.val.val ∩ O.val := by simpa only [D.property] using hi
      exact (Finset.mem_inter.mp hm).1
    · intro i hi
      have hm : i ∈ E.val.val ∩ O.val := by simpa only [E.property] using hi
      exact (Finset.mem_inter.mp hm).1
  have hl := Finset.card_le_card hs
  rw [hS] at hl
  have h8 : (D.val.val ∩ E.val.val).card ≠ 8 := by
    intro h
    apply hne
    apply Subtype.ext
    apply Subtype.ext
    have hd : D.val.val ∩ E.val.val=D.val.val :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h,octad_size _ D.val.property])
    have he : D.val.val ∩ E.val.val=E.val.val :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [h,octad_size _ E.val.property])
    exact hd.symm.trans he
  omega

end Atlas.Fischer
