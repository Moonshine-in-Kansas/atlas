import Atlas.Fischer.OctadicHyperplanePairings

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

def octadicFortySixGenerators {O : Octad} (Q : OctadCalibration O) : Set Coordinates :=
  Set.range (fun i : OctadExterior O => u i.val) ∪ Set.range (calibratedHyperplaneVector Q)

def octadicFortySixSpace {O : Octad} (Q : OctadCalibration O) : Submodule Scalar Coordinates :=
  Submodule.span Scalar (octadicFortySixGenerators Q)

theorem rootMap_octadic_fortySix_invariant {O : Octad} (Q : OctadCalibration O) :
    Set.MapsTo (rootMap (octadicRoot Q 0)) (octadicFortySixSpace Q) (octadicFortySixSpace Q) := by
  have hu (i : Omega) (hi : i ∉ O.val) : u i ∈ octadicFortySixSpace Q :=
    Submodule.subset_span (Or.inl ⟨⟨i, hi⟩, rfl⟩)
  have hy (b : OctadShortenedHyperplane O) :
      calibratedHyperplaneVector Q b ∈ octadicFortySixSpace Q :=
    Submodule.subset_span (Or.inr ⟨b, rfl⟩)
  have hs : octadExteriorAxisSum O ∈ octadicFortySixSpace Q :=
    (octadicFortySixSpace Q).sum_mem (fun i hi => hu i (Finset.mem_compl.mp hi))
  have hY (χ : OctadicCharacter O) : octadicHyperplanePart Q χ ∈ octadicFortySixSpace Q :=
    (octadicFortySixSpace Q).sum_mem (fun b _ => (octadicFortySixSpace Q).smul_mem _ (hy b))
  have hb (b : OctadShortenedHyperplane O) :
      octadicHyperplaneAxisSum Q b ∈ octadicFortySixSpace Q := by
    unfold octadicHyperplaneAxisSum octadAxisSum
    apply (octadicFortySixSpace Q).sum_mem
    intro i hi
    apply hu
    intro hio
    exact Finset.disjoint_left.mp (calibratedHyperplaneSupport_disjoint Q b) hio hi
  apply rootMap_invariant_span
  intro x hx
  rcases hx with ⟨i, rfl⟩ | ⟨b, rfl⟩
  · rw [rootMap_octadic_outside_axis]
    exact (octadicFortySixSpace Q).smul_mem _ ((octadicFortySixSpace Q).sub_mem hs (hY _))
  · rw [rootMap_octadic_hyperplane]
    exact (octadicFortySixSpace Q).smul_mem _ ((octadicFortySixSpace Q).add_mem
      ((octadicFortySixSpace Q).add_mem ((octadicFortySixSpace Q).sub_mem
        ((octadicFortySixSpace Q).smul_mem _ (hb b)) hs) (hy b)) (hy _))

theorem rootMap_octadic_fortySix_antiunitary {O : Octad} (Q : OctadCalibration O) :
    RootMapAntiunitaryOn (octadicRoot Q 0) (octadicFortySixSpace Q) := by
  apply rootMap_antiunitary_span
  intro x hx y hy
  rcases hx with ⟨i, rfl⟩ | ⟨b, rfl⟩ <;> rcases hy with ⟨j, rfl⟩ | ⟨c, rfl⟩
  · exact rootMap_octadic_exterior_axis_pairing Q i j
  · rw [rootMap_octadic_exterior_hyperplane_pairing]
    simp only [calibratedHyperplaneVector, hermitian_u_signedOctad, star_zero]
  · rw [← hermitian_star, rootMap_octadic_exterior_hyperplane_pairing]
    simp only [calibratedHyperplaneVector, hermitian_signedOctad_u, star_zero]
  · exact rootMap_octadic_hyperplane_pairing Q b c

theorem rootMap_octadic_fortySix_involutive {O : Octad} (Q : OctadCalibration O)
    (x : Coordinates) (hx : x ∈ octadicFortySixSpace Q) :
    rootMap (octadicRoot Q 0) (rootMap (octadicRoot Q 0) x) = x :=
  rootMap_involutive_on_of_antiunitaryOn _ _ (rootMap_octadic_fortySix_invariant Q)
    (rootMap_octadic_fortySix_antiunitary Q) x hx

end Atlas.Fischer
