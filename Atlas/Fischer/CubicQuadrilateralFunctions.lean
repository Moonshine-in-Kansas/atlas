import Atlas.Fischer.CubicQuadrilateralWeights
import Atlas.Fischer.CubicWeightedIncidenceAverages

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

def cubicQuadrilateralNormalizedWeight (D F G : Octad) : Scalar :=
  if hDF : OctadPairAdmissible D F then
    if hDG : OctadPairAdmissible D G then
      if hFG : OctadPairAdmissible F G then
        16 * cubicOctadQuadrilateralWeight D F G hDF hDG hFG
      else 0
    else 0
  else 0

def cubicQuadrilateralLabel (F G : Octad) : Octad :=
  if hFG : OctadPairAdmissible F G then octadDiamond F G hFG else F

theorem cubicOctadPairAdmissible_smul (g : Mathieu24CodeModel) (D F : Octad) :
    OctadPairAdmissible (g • D) (g • F) ↔ OctadPairAdmissible D F := by
  simp only [OctadPairAdmissible,cubicCommonNeighbor_pair_card]

theorem cubicOctadDiamond_smul (g : Mathieu24CodeModel) (F G : Octad)
    (h : OctadPairAdmissible F G) :
    octadDiamond (g • F) (g • G) ((cubicOctadPairAdmissible_smul g F G).mpr h) =
      g • octadDiamond F G h := by
  apply octadWord_injective
  rw [octadDiamond_word,cubicTriangle_word_smul,cubicTriangle_word_smul,
    cubicTriangle_word_smul,octadDiamond_word,cubicCommonNeighbor_pair_card]
  simp only [map_add]
  split_ifs <;> simp [cubicTriangle_one_fixed]

theorem cubicQuadrilateralLabel_smul (g : Mathieu24CodeModel) (F G : Octad) :
    cubicQuadrilateralLabel (g • F) (g • G) = g • cubicQuadrilateralLabel F G := by
  by_cases h : OctadPairAdmissible F G
  · simp only [cubicQuadrilateralLabel,dif_pos h,
      dif_pos ((cubicOctadPairAdmissible_smul g F G).mpr h)]
    exact cubicOctadDiamond_smul g F G h
  · simp [cubicQuadrilateralLabel,h,cubicOctadPairAdmissible_smul]

theorem cubicQuadrilateralNormalizedWeight_smul (g : Mathieu24CodeModel) (D F G : Octad) :
    cubicQuadrilateralNormalizedWeight (g • D) (g • F) (g • G) =
      cubicQuadrilateralNormalizedWeight D F G := by
  by_cases hDF : OctadPairAdmissible D F
  · by_cases hDG : OctadPairAdmissible D G
    · by_cases hFG : OctadPairAdmissible F G
      · simp only [cubicQuadrilateralNormalizedWeight,dif_pos hDF,dif_pos hDG,dif_pos hFG,
          dif_pos ((cubicOctadPairAdmissible_smul g D F).mpr hDF),
          dif_pos ((cubicOctadPairAdmissible_smul g D G).mpr hDG),
          dif_pos ((cubicOctadPairAdmissible_smul g F G).mpr hFG)]
        rw [cubicOctadQuadrilateralWeight_formula,cubicOctadQuadrilateralWeight_formula,
          cubicQuadrilateral_delta (g • D) (g • F) (g • G) _ _
            ((cubicOctadPairAdmissible_smul g F G).mpr hFG),
          cubicQuadrilateral_delta D F G hDF hDG hFG]
        simp only [octadDelta,cubicCommonNeighbor_pair_card,cubicCommonNeighbor_triple_card]
      · simp [cubicQuadrilateralNormalizedWeight,hDF,hDG,hFG,cubicOctadPairAdmissible_smul]
    · simp [cubicQuadrilateralNormalizedWeight,hDF,hDG,cubicOctadPairAdmissible_smul]
  · simp [cubicQuadrilateralNormalizedWeight,hDF,cubicOctadPairAdmissible_smul]

end Atlas.Fischer
