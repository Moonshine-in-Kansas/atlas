import Atlas.Fischer.OctadScalarBlockGeometry
import Atlas.Fischer.OctadicNineDimension
import Atlas.Fischer.OctadicFortySixDimension

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual duad labels of the sixteen-dimensional blocks. -/
def octadDuadLabels (O : Octad) : Finset (Finset Omega) := O.val.powersetCard 2

/-- Choose one label of each complementary tetrad pair by a marked point. -/
def octadTetradLabels (O : Octad) (i : O.val) : Finset (Finset Omega) :=
  (O.val.powersetCard 4).filter (fun S => {i.val} ⊆ S)

theorem octadDuadLabels_card (O : Octad) : (octadDuadLabels O).card = 28 := by
  rw [octadDuadLabels, Finset.card_powersetCard, octad_size O.val O.prop]
  decide

theorem octadTetradLabels_card (O : Octad) (i : O.val) :
    (octadTetradLabels O i).card = 35 := by
  rw [octadTetradLabels, Finset.card_filter_powersetCard_subset]
  · rw [octad_size O.val O.prop, Finset.card_singleton]
    decide
  · exact Finset.singleton_subset_iff.mpr i.prop
  · simp

/-- Each tetrad block has a label in the selected set of thirty-five. -/
theorem octadTetradLabels_cover (O : Octad) (i : O.val) (S : Finset Omega)
    (hSO : S ⊆ O.val) (hS : S.card = 4) :
    ∃ T ∈ octadTetradLabels O i, octadScalarBlock O S = octadScalarBlock O T := by
  classical
  by_cases hi : i.val ∈ S
  · refine ⟨S, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hSO, hS⟩,
      Finset.singleton_subset_iff.mpr hi⟩
  · refine ⟨O.val \ S, ?_, (octadScalarBlock_complement O S hSO).symm⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset, ?_⟩,
      Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mpr ⟨i.prop, hi⟩)⟩
    rw [Finset.card_sdiff_of_subset hSO, octad_size O.val O.prop, hS]

/-- Complementary tetrads cannot both belong to the selected representatives. -/
theorem octadTetradLabels_not_complement (O : Octad) (i : O.val)
    {S T : Finset Omega} (hS : S ∈ octadTetradLabels O i)
    (hT : T ∈ octadTetradLabels O i) : O.val \ S ≠ T := by
  intro h
  have hiS := Finset.singleton_subset_iff.mp (Finset.mem_filter.mp hS).2
  have hiT := Finset.singleton_subset_iff.mp (Finset.mem_filter.mp hT).2
  rw [← h] at hiT
  exact (Finset.mem_sdiff.mp hiT).2 hiS

/-- The dimension identity uses the counted actual label families and actual small spaces. -/
theorem octadicBlock_dimension_total {O : Octad} (Q : OctadCalibration O) (i : O.val) :
    Module.finrank Scalar (octadicNineSpace Q) +
      Module.finrank Scalar (octadicFortySixSpace Q) +
      (octadDuadLabels O).card * 16 + (octadTetradLabels O i).card * 8 =
        Module.finrank Scalar Coordinates := by
  rw [octadicNineSpace_dimension, octadicFortySixSpace_dimension,
    octadDuadLabels_card, octadTetradLabels_card, coordinates_dimension]

end Atlas.Fischer
