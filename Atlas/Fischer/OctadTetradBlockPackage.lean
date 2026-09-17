import Atlas.Fischer.OctadTetradMatrixIsometry
import Atlas.Fischer.RootMapSubspaces

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem rootMap_octadic_tetrad_invariant {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hTO : T ⊆ O.val) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val) :
    Set.MapsTo (rootMap (octadicRoot Q 0)) (octadScalarBlock O T) (octadScalarBlock O T) := by
  rw [← octadTetradPairedFamily_span Q T hTO hT D d hd]
  apply rootMap_invariant_span
  rintro x ⟨p,rfl⟩
  rw [rootMap_octadic_tetrad_row Q T hTO hT D d hd p]
  apply Submodule.add_mem
  all_goals
    apply Submodule.smul_mem
    apply Submodule.sub_mem
    · apply Submodule.sum_mem
      intro j hj
      exact Submodule.subset_span ⟨_,rfl⟩
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨_,rfl⟩

theorem rootMap_octadic_tetrad_antiunitary {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hTO : T ⊆ O.val) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val) :
    RootMapAntiunitaryOn (octadicRoot Q 0) (octadScalarBlock O T) := by
  rw [← octadTetradPairedFamily_span Q T hTO hT D d hd]
  apply rootMap_antiunitary_span
  rintro x ⟨p,rfl⟩ y ⟨q,rfl⟩
  rw [rootMap_octadic_tetrad_pairing Q T hTO hT D d hd p q,
    octadTetradPairedFamily_orthonormal Q T hTO hT D d hd p q]
  split_ifs <;> simp

/-- Invariance of the actual eight-dimensional Leech/Golay tetrad block. -/
theorem rootMap_octadic_tetrad_block_invariant {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hTO : T ⊆ O.val) (hT : T.card = 4) :
    Set.MapsTo (rootMap (octadicRoot Q 0)) (octadScalarBlock O T) (octadScalarBlock O T) := by
  obtain ⟨D,hD⟩ := exists_octad_with_restriction O T hTO (Or.inr hT)
  exact rootMap_octadic_tetrad_invariant Q T hTO hT ⟨D,hD⟩ (canonicalOctadLift D).val rfl

/-- Antiunitarity for that same actual block, with no matrix or sign hypothesis. -/
theorem rootMap_octadic_tetrad_block_antiunitary {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hTO : T ⊆ O.val) (hT : T.card = 4) :
    RootMapAntiunitaryOn (octadicRoot Q 0) (octadScalarBlock O T) := by
  obtain ⟨D,hD⟩ := exists_octad_with_restriction O T hTO (Or.inr hT)
  exact rootMap_octadic_tetrad_antiunitary Q T hTO hT ⟨D,hD⟩ (canonicalOctadLift D).val rfl

end Atlas.Fischer
