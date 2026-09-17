import Atlas.Fischer.OctadScalarBlockGeometry
import Atlas.Fischer.OctadicNineDimension
import Atlas.Fischer.OctadicFortySixDimension
import Atlas.Fischer.RootMapOrthogonalSum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem octadicNineSpace_le_zeroBlock {O : Octad} (Q : OctadCalibration O) :
    octadicNineSpace Q ≤ octadScalarBlock O ∅ := by
  apply Submodule.span_le.mpr
  rintro x (⟨i,rfl⟩ | rfl)
  · exact coordinateVector_mem_octadScalarBlock O ∅ (.inl i.val) ⟨0,rfl⟩
  · unfold signedOctadVector
    apply Submodule.smul_mem
    unfold xOctad
    apply coordinateVector_mem_octadScalarBlock
    have ho : signedOctadSupport Q.octadLift=O := (signedOctadSupport_eq_iff _ _).mpr Q.lift_code
    exact ⟨1,by simp [ho,octadRationalLabel]⟩

theorem octadicFortySixSpace_le_zeroBlock {O : Octad} (Q : OctadCalibration O) :
    octadicFortySixSpace Q ≤ octadScalarBlock O ∅ := by
  apply Submodule.span_le.mpr
  rintro x (⟨i,rfl⟩ | ⟨b,rfl⟩)
  · exact coordinateVector_mem_octadScalarBlock O ∅ (.inl i.val) ⟨0,rfl⟩
  · unfold calibratedHyperplaneVector signedOctadVector
    apply Submodule.smul_mem
    unfold xOctad
    apply coordinateVector_mem_octadScalarBlock
    refine ⟨0,?_⟩
    change (signedOctadSupport (calibratedHyperplaneLift Q b)).val ∩ O.val=∅
    exact Finset.disjoint_iff_inter_eq_empty.mp (calibratedHyperplaneSupport_disjoint Q b).symm

theorem octadicNineFortySix_orthogonal {O : Octad} (Q : OctadCalibration O) :
    HermitianOrthogonalSubspaces (octadicNineSpace Q) (octadicFortySixSpace Q) := by
  apply hermitianOrthogonal_span
  rintro x (⟨i,rfl⟩ | rfl) y (⟨j,rfl⟩ | ⟨b,rfl⟩)
  · have hij : i.val ≠ j.val := fun h => j.prop (h ▸ i.prop)
    rw [hermitian_u,if_neg hij]
  · exact hermitian_u_signedOctad _ _
  · exact hermitian_signedOctad_u _ _
  · exact hermitian_octad_calibratedHyperplane Q b

/-- The actual 55-dimensional zero/complement block is the orthogonal sum of
the already verified nine- and forty-six-dimensional subspaces. -/
theorem octadicNine_sup_fortySix {O : Octad} (Q : OctadCalibration O) :
    octadicNineSpace Q ⊔ octadicFortySixSpace Q=octadScalarBlock O ∅ := by
  apply Submodule.eq_of_le_of_finrank_le
    (sup_le (octadicNineSpace_le_zeroBlock Q) (octadicFortySixSpace_le_zeroBlock Q))
  have hd := (octadicNineFortySix_orthogonal Q).disjoint
  have he := Submodule.finrank_sup_add_finrank_inf_eq (octadicNineSpace Q) (octadicFortySixSpace Q)
  rw [hd.eq_bot,finrank_bot,add_zero,octadicNineSpace_dimension,
    octadicFortySixSpace_dimension] at he
  rw [octadScalarBlock_empty_dimension,he]

theorem rootMap_octadic_zeroBlock_invariant {O : Octad} (Q : OctadCalibration O) :
    Set.MapsTo (rootMap (octadicRoot Q 0)) (octadScalarBlock O ∅) (octadScalarBlock O ∅) := by
  rw [← octadicNine_sup_fortySix Q]
  exact rootMap_invariant_sup _ _ _ (rootMap_octadic_nine_invariant Q)
    (rootMap_octadic_fortySix_invariant Q)

theorem rootMap_octadic_zeroBlock_antiunitary {O : Octad} (Q : OctadCalibration O) :
    RootMapAntiunitaryOn (octadicRoot Q 0) (octadScalarBlock O ∅) := by
  rw [← octadicNine_sup_fortySix Q]
  exact rootMap_antiunitary_sup _ _ _ (rootMap_octadic_nine_invariant Q)
    (rootMap_octadic_fortySix_invariant Q) (rootMap_octadic_nine_antiunitary Q)
    (rootMap_octadic_fortySix_antiunitary Q) (octadicNineFortySix_orthogonal Q)

end Atlas.Fischer
