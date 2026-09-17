import Atlas.Fischer.OctadFibreHyperplaneEquiv
import Atlas.Fischer.OctadicCrossingExpansion

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem octadFibreRow_signed_intersection {O : Octad} (Q : OctadCalibration O)
    (S : Finset Omega) (E : OctadIntersectionFibre O S) (d : SignedOctad)
    (hd : d.val.1 = octadWord E.val) (b : OctadFibreRowHyperplanes O S E) :
    signedOctadIntersection d (calibratedHyperplaneLift Q b.val) = 4 := by
  rw [signedOctadIntersection_overlap, hd]
  exact b.property

theorem signedOctadFourContribution_row {O : Octad} (Q : OctadCalibration O)
    (S : Finset Omega) (E : OctadIntersectionFibre O S) (d : SignedOctad)
    (hd : d.val.1 = octadWord E.val) (b : OctadFibreRowHyperplanes O S E) :
    signedOctadFourContribution d (calibratedHyperplaneLift Q b.val) =
      signedOctadVector (octadProductFour d (calibratedHyperplaneLift Q b.val)
        (octadFibreRow_signed_intersection Q S E d hd b)) := by
  rw [signedOctadFourContribution, dif_pos (octadFibreRow_signed_intersection Q S E d hd b)]

/-- The dependent-if scalar contribution is exactly the sum on its actual overlap-four domain. -/
theorem sum_signedOctadFourContribution_subtype {O : Octad} (Q : OctadCalibration O)
    (S : Finset Omega) (E : OctadIntersectionFibre O S) (d : SignedOctad)
    (hd : d.val.1 = octadWord E.val) :
    (∑ b : OctadShortenedHyperplane O, signedOctadFourContribution d (calibratedHyperplaneLift Q b)) =
      ∑ b : OctadFibreRowHyperplanes O S E,
        signedOctadFourContribution d (calibratedHyperplaneLift Q b.val) := by
  symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro b hb
    have hn : signedOctadIntersection d (calibratedHyperplaneLift Q b) ≠ 4 := by
      intro h
      rw [signedOctadIntersection_overlap, hd] at h
      exact hb ⟨⟨b, h⟩, rfl⟩
    rw [signedOctadFourContribution, dif_neg hn]
  · intro b
    rfl

/-- Any exact row-to-column label identity transports the source contribution
sum to all other actual members of the same fibre. -/
theorem octadFibreRow_sum {M : Type*} [AddCommGroup M] (O : Octad) (S : Finset Omega)
    (E : OctadIntersectionFibre O S)
    (hrow : ∀ F : OctadIntersectionFibre O S, F ≠ E → (E.val.val ∩ F.val.val).card = 4)
    (G : OctadShortenedHyperplane O → M) (v : OctadIntersectionFibre O S → M)
    (hv : ∀ (F : OctadIntersectionFibre O S) (hF : F ≠ E),
      G (octadFibreSumHyperplane O S E F (hrow F hF)) = v F) :
    (∑ b : OctadFibreRowHyperplanes O S E, G b.val) = (∑ F, v F) - v E := by
  letI : Fintype {F : OctadIntersectionFibre O S // F ≠ E} := Fintype.ofFinite _
  let e := octadFibreRowHyperplaneEquiv O S E hrow
  rw [← e.symm.sum_comp (fun b => G b.val)]
  have hh : (∑ F : {F : OctadIntersectionFibre O S // F ≠ E}, G (e.symm F).val) =
      ∑ F : {F : OctadIntersectionFibre O S // F ≠ E}, v F.val := by
    apply Finset.sum_congr rfl
    intro F hF
    exact hv F.val F.property
  rw [hh]
  have he : (∑ F : {F : OctadIntersectionFibre O S // F ≠ E}, v F.val) =
      ∑ F ∈ (Finset.univ.erase E : Finset (OctadIntersectionFibre O S)), v F := by
    symm
    apply Finset.sum_subtype
    intro F
    simp
  rw [he]
  exact eq_sub_iff_add_eq.mpr (Finset.sum_erase_add Finset.univ v (Finset.mem_univ E))

end Atlas.Fischer
