import Atlas.Fischer.QuinticMixedCriterion
import Atlas.Fischer.QuinticPointOctadConfigurations
import Atlas.Fischer.CubicQuadrilateralPointAverages

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Exact comparison of the literal E block with the proved signed configuration sum. -/
theorem quinticPointOctadWWW_WWW_normalized_sum (p : Omega) (D : Octad) :
    quinticPointOctadWWW_WWW p D =
      (1 / 256 : Scalar) * ∑ J : Octad, ∑ K : Octad,
        cubicQuadrilateralNormalizedWeight D J K *
          cubicPointOctadIncidence p (cubicQuadrilateralLabel J K) := by
  rw [quinticPointOctadWWW_WWW_configurations]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro K hK
  unfold cubicQuadrilateralNormalizedWeight cubicQuadrilateralLabel
  by_cases hDJ : OctadPairAdmissible D J <;>
    by_cases hDK : OctadPairAdmissible D K <;>
    by_cases hJK : OctadPairAdmissible J K <;>
    simp [hDJ,hDK,hJK] <;> ring

/-- The two numerical pure-octad contributions, derived from all signed configurations. -/
theorem quinticPointOctadWWW_WWW_ratio (p : Omega) (D : Octad) :
    quinticPointOctadWWW_WWW p D =
      (if p ∈ D.val then (6015 / 8 : Scalar) else 6855 / 8) *
        coordinateCubic (.inl p) (.inr D) (.inr D) := by
  rw [quinticPointOctadWWW_WWW_normalized_sum, cubicQuadrilateral_point_sum,
    coordinateCubic_point_octads]
  by_cases hp : p ∈ D.val <;> norm_num [cubicPointOctadIncidence,hp]

/-- Uniform actual repeated-octad identity, without an unproved tensor hypothesis. -/
theorem coordinateQuintic_point_repeated_octad (p : Omega) (D : Octad) :
    coordinateQuintic (.inl p) (.inr D) (.inr D) =
      1002 * coordinateCubic (.inl p) (.inr D) (.inr D) := by
  rw [coordinateQuintic_point_octad_reduced, quinticPointOctadWWW_WWW_ratio]
  by_cases hp : p ∈ D.val <;> simp only [hp,ite_true,ite_false] <;> ring

/-- All actual point/two-octad entries, including the vanishing off-diagonal entries. -/
theorem coordinateQuintic_point_octads (p : Omega) (D E : Octad) :
    coordinateQuintic (.inl p) (.inr D) (.inr E) =
      1002 * coordinateCubic (.inl p) (.inr D) (.inr E) := by
  by_cases hDE : D = E
  · subst E
    exact coordinateQuintic_point_repeated_octad p D
  · rw [coordinateQuintic_point_distinct_octads p D E hDE,
      coordinateCubic_point_octads, if_neg hDE, mul_zero]

theorem coordinateQuintic_octad_point_octad (D : Octad) (p : Omega) (E : Octad) :
    coordinateQuintic (.inr D) (.inl p) (.inr E) =
      1002 * coordinateCubic (.inr D) (.inl p) (.inr E) := by
  rw [coordinateQuintic_swap_first, coordinateCubic_swap_first,
    coordinateQuintic_point_octads]

theorem coordinateQuintic_octads_point (D E : Octad) (p : Omega) :
    coordinateQuintic (.inr D) (.inr E) (.inl p) =
      1002 * coordinateCubic (.inr D) (.inr E) (.inl p) := by
  rw [coordinateQuintic_swap_last, coordinateCubic_swap_last,
    coordinateQuintic_octad_point_octad]

end Atlas.Fischer
