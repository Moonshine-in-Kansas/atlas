import Atlas.Fischer.OctadQuadraticQuotient

namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra

@[simp] theorem octadEvenOne_apply (O : Octad) (i : O.val) : (octadEvenOne O).val i=1 := by
  change (octadWord O).val i.val=1
  simp [octadWord_apply,i.property]

theorem octadEvenOne_ne_zero (O : Octad) : octadEvenOne O ≠ 0 := by
  intro h
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < O.val.card by
    rw [octad_size O.val O.property]; decide)
  have he := congrArg (fun x : octadEvenCode O => x.val ⟨i,hi⟩) h
  exact one_ne_zero (by simpa only [octadEvenOne_apply,Submodule.coe_zero,Pi.zero_apply] using he)

theorem octadEvenClasses_finrank (O : Octad) : Module.finrank Bit (OctadEvenClasses O)=6 := by
  have hc : Module.finrank Bit (octadEvenConstants O)=1 :=
    finrank_span_singleton (octadEvenOne_ne_zero O)
  have h := (octadEvenConstants O).finrank_quotient_add_finrank
  rw [hc,octadEvenCode_finrank] at h
  change Module.finrank Bit (OctadEvenClasses O)+1=7 at h
  omega

theorem binaryQuadraticClasses_finrank (O : Octad) : Module.finrank Bit BinaryQuadraticClasses=6 := by
  rw [← (octadEvenQuadraticClassesEquiv O).finrank_eq,octadEvenClasses_finrank]

/-- Exact coordinate compatibility of the quotient isomorphism: both classes
come from the same retained Golay word, restricted to complementary coordinates. -/
theorem octadEvenQuadraticClassesEquiv_apply (O : Octad) (c : golay) :
    octadEvenQuadraticClassesEquiv O (octadEvenClassMap O c) = octadQuadraticClassMap O c := by
  simp only [octadEvenQuadraticClassesEquiv,LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply,Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

end Atlas.Fischer
