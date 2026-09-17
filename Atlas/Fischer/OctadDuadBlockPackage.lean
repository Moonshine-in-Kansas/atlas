import Atlas.Fischer.OctadDuadRootMap

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem rootMap_octadic_duad_block_invariant {O : Octad} (Q : OctadCalibration O)
    (S : Finset Omega) (hSO : S ⊆ O.val) (hS : S.card=2) :
    Set.MapsTo (rootMap (octadicRoot Q 0)) (octadScalarBlock O S) (octadScalarBlock O S) := by
  obtain ⟨D,hD⟩ := exists_octad_with_restriction O S hSO (Or.inl hS)
  let d := canonicalOctadLift D
  have hds : support d.val.1.val ∩ O.val=S := by
    change support (octadWord D).val ∩ O.val=S
    rw [octadWord_support,hD]
  have hd : (support d.val.1.val ∩ O.val).card=2 := by rw [hds,hS]
  simpa only [hds] using rootMap_octadic_duad_invariant Q d hd

theorem rootMap_octadic_duad_block_antiunitary {O : Octad} (Q : OctadCalibration O)
    (S : Finset Omega) (hSO : S ⊆ O.val) (hS : S.card=2) :
    RootMapAntiunitaryOn (octadicRoot Q 0) (octadScalarBlock O S) := by
  obtain ⟨D,hD⟩ := exists_octad_with_restriction O S hSO (Or.inl hS)
  let d := canonicalOctadLift D
  have hds : support d.val.1.val ∩ O.val=S := by
    change support (octadWord D).val ∩ O.val=S
    rw [octadWord_support,hD]
  have hd : (support d.val.1.val ∩ O.val).card=2 := by rw [hds,hS]
  simpa only [hds] using rootMap_octadic_duad_antiunitary Q d hd

end Atlas.Fischer
