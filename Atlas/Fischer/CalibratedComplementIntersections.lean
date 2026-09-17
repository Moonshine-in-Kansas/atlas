import Atlas.Fischer.CalibratedComplementLabels
import Atlas.Fischer.OctadicMixedAxisProducts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem calibratedHyperplaneSupport_complement {O : Octad} (Q : OctadCalibration O)
    (c : OctadShortenedHyperplane O) :
    (signedOctadSupport (calibratedHyperplaneLift Q (octadHyperplaneComplement O c))).val =
      O.valᶜ \ (signedOctadSupport (calibratedHyperplaneLift Q c)).val := by
  change support (c.val.val.val + (octadComplementWord O).val) = O.valᶜ \ support c.val.val.val
  ext i
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
    Finset.mem_compl, Pi.add_apply]
  rw [octadComplementWord_apply]
  by_cases ho : i ∈ O.val
  · have hz := (mem_octadShortenedCode O c.val.val).mp c.val.property i ho
    simp [ho, hz]
  · simp only [ite_eq_right ho, ho, not_false_eq_true, true_and]
    exact (show ∀ b : Bit, b + 1 ≠ 0 ↔ ¬b ≠ 0 by decide) _

/-- Intersections with complementary exterior hyperplanes partition the actual
four exterior points of a tetrad-crossing octad. -/
theorem calibratedHyperplane_complement_intersections {O : Octad} (Q : OctadCalibration O)
    (d : SignedOctad) (hD : ((signedOctadSupport d).val ∩ O.val).card = 4)
    (c : OctadShortenedHyperplane O) :
    signedOctadIntersection d (calibratedHyperplaneLift Q c) +
      signedOctadIntersection d (calibratedHyperplaneLift Q (octadHyperplaneComplement O c)) = 4 := by
  unfold signedOctadIntersection
  rw [calibratedHyperplaneSupport_complement]
  have hB : (signedOctadSupport (calibratedHyperplaneLift Q c)).val ⊆ O.valᶜ := by
    intro i hi
    exact Finset.mem_compl.mpr (fun ho =>
      Finset.disjoint_left.mp (calibratedHyperplaneSupport_disjoint Q c) ho hi)
  have hs : (signedOctadSupport d).val ∩ (signedOctadSupport (calibratedHyperplaneLift Q c)).val ⊆
      (signedOctadSupport d).val ∩ O.valᶜ :=
    fun i hi => Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1, hB (Finset.mem_inter.mp hi).2⟩
  have he : (signedOctadSupport d).val ∩
      (O.valᶜ \ (signedOctadSupport (calibratedHyperplaneLift Q c)).val) =
      ((signedOctadSupport d).val ∩ O.valᶜ) \
        ((signedOctadSupport d).val ∩ (signedOctadSupport (calibratedHyperplaneLift Q c)).val) := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    tauto
  rw [he, add_comm, Finset.card_sdiff_add_card_eq_card hs, ← Finset.sdiff_eq_inter_compl,
    Finset.card_sdiff, Finset.inter_comm, hD, octad_size _ (signedOctadSupport d).property]

theorem calibratedHyperplane_complement_disjoint_iff {O : Octad} (Q : OctadCalibration O)
    (d : SignedOctad) (hD : ((signedOctadSupport d).val ∩ O.val).card = 4)
    (c : OctadShortenedHyperplane O) :
    signedOctadIntersection d (calibratedHyperplaneLift Q (octadHyperplaneComplement O c)) = 0 ↔
      signedOctadIntersection d (calibratedHyperplaneLift Q c) = 4 := by
  have h := calibratedHyperplane_complement_intersections Q d hD c
  omega

end Atlas.Fischer
