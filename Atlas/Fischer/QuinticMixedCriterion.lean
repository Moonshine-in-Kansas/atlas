import Atlas.Fischer.QuinticPointOctadReduction
import Atlas.Fischer.QuinticPointOctadNetwork
import Atlas.Fischer.CubicSupportTypes

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Conditional arithmetic closure; the signed network moment is an explicit obligation. -/
theorem quinticPointOctadWWW_WWW_ratio_of_network (p : Omega) (D : Octad)
    (h : (16 : Scalar) * ∑ I : Octad,
      cubicPointOctadIncidence p I * cubicOctadQuadrilateralNetwork D I =
        if p ∈ D.val then 36090 else -13710) :
    quinticPointOctadWWW_WWW p D =
      (if p ∈ D.val then (6015 / 8 : Scalar) else 6855 / 8) *
        coordinateCubic (.inl p) (.inr D) (.inr D) := by
  rw [quinticPointOctadWWW_WWW_network, coordinateCubic_point_octads]
  by_cases hp : p ∈ D.val
  · simp only [hp, ite_true] at h ⊢
    rw [show cubicPointOctadIncidence p D = 3 by simp [cubicPointOctadIncidence, hp]]
    linear_combination h / 256
  · simp only [hp, ite_false, ite_true] at h ⊢
    rw [show cubicPointOctadIncidence p D = -1 by simp [cubicPointOctadIncidence, hp]]
    linear_combination h / 256

/-- The public repeated-octad tensor identity, conditional only on its explicit
remaining signed-network value. No universal quintic identity is assumed. -/
theorem coordinateQuintic_point_repeated_octad_of_network (p : Omega) (D : Octad)
    (h : (16 : Scalar) * ∑ I : Octad,
      cubicPointOctadIncidence p I * cubicOctadQuadrilateralNetwork D I =
        if p ∈ D.val then 36090 else -13710) :
    coordinateQuintic (.inl p) (.inr D) (.inr D) =
      1002 * coordinateCubic (.inl p) (.inr D) (.inr D) := by
  rw [coordinateQuintic_point_octad_reduced,
    quinticPointOctadWWW_WWW_ratio_of_network p D h]
  by_cases hp : p ∈ D.val <;> simp only [hp, ite_true, ite_false] <;> ring

/-- All other point/two-octad entries vanish by actual cocode support. -/
theorem coordinateQuintic_point_distinct_octads (p : Omega) (D E : Octad) (hDE : D ≠ E) :
    coordinateQuintic (.inl p) (.inr D) (.inr E) = 0 := by
  by_contra hn
  have hs := coordinateQuintic_nonzero_support (.inl p) (.inr D) (.inr E) hn
  change 0 + octadWord D + octadWord E ∈ allOneCodeLine at hs
  simp only [zero_add] at hs
  rcases (mem_allOneCodeLine _).mp hs with hz | ho
  · apply hDE
    apply octadWord_injective
    have he := congrArg (fun c : golay => c + octadWord E) hz
    simpa only [add_assoc, parkerGolay_add_self, add_zero, zero_add] using he
  · exact productTraceCoordinateWord_sum_ne_one (.inr D) (.inr E) ho

/-- Uniform mixed tensor identity, retaining the exact remaining network hypothesis. -/
theorem coordinateQuintic_point_octads_of_network
    (h : ∀ (p : Omega) (D : Octad), (16 : Scalar) * ∑ I : Octad,
      cubicPointOctadIncidence p I * cubicOctadQuadrilateralNetwork D I =
        if p ∈ D.val then 36090 else -13710)
    (p : Omega) (D E : Octad) :
    coordinateQuintic (.inl p) (.inr D) (.inr E) =
      1002 * coordinateCubic (.inl p) (.inr D) (.inr E) := by
  by_cases hDE : D = E
  · subst E
    exact coordinateQuintic_point_repeated_octad_of_network p D (h p D)
  · rw [coordinateQuintic_point_distinct_octads p D E hDE,
      coordinateCubic_point_octads, if_neg hDE, mul_zero]

end Atlas.Fischer
