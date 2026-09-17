import Atlas.Fischer.CubicPointBlockBilinear
import Atlas.Fischer.CubicTriangleCounts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The point-cubic coefficient of a literal sextet completion. -/
theorem coordinateCubic_point_sextet_completion (p : Omega) (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E) :
    (∑ a : Omega, ∑ b : Omega, coordinateCubic (.inl p) (.inl a) (.inl b) *
      cubicPointOctadIncidence a E * cubicPointOctadIncidence b F) =
      if p ∈ D.val then (15 / 16 : Scalar) else -1 / 16 := by
  have hD : octadWord D = octadWord E + octadWord F := by
    rw [hF, ← add_assoc, add_comm (octadWord E) (octadWord D), add_assoc,
      parkerGolay_add_self, add_zero]
  have hi : (E.val ∩ F.val).card = 4 := by
    simpa only [signedOctadIntersection, signedOctadSupport_canonical] using
      octadWord_sum_weight D E F hD
  rw [coordinateCubic_point_octad_bilinear, cubicPointOctadIncidence_overlap_sum, hi]
  have h := congrArg (fun c : golay => c.val p) hF
  simp only [Submodule.coe_add, Pi.add_apply, octadWord_apply] at h
  by_cases hDp : p ∈ D.val <;> by_cases hEp : p ∈ E.val <;>
    by_cases hFp : p ∈ F.val <;>
    simp [hDp, hEp, hFp, show (2 : Bit) = 0 from rfl] at h <;>
    norm_num [cubicPointOctadIncidence, hDp, hEp, hFp]

/-- The point-cubic coefficient of a literal trio completion. -/
theorem coordinateCubic_point_trio_completion (p : Omega) (D E F : Octad)
    (hF : octadWord F = octadWord D + octadWord E + golayOne) :
    (∑ a : Omega, ∑ b : Omega, coordinateCubic (.inl p) (.inl a) (.inl b) *
      cubicPointOctadIncidence a E * cubicPointOctadIncidence b F) =
      if p ∈ D.val then (-17 / 16 : Scalar) else -1 / 16 := by
  have hD : octadWord D = octadWord E + octadWord F + golayOne := by
    rw [hF]
    symm
    calc
      _ = octadWord D + (octadWord E + octadWord E) + (golayOne + golayOne) := by abel
      _ = octadWord D := by simp only [parkerGolay_add_self, add_zero]
  have hi : (E.val ∩ F.val).card = 0 := by
    simpa only [signedOctadIntersection, signedOctadSupport_canonical] using
      octadWord_complementary_sum_weight D E F hD
  have hEF : ¬ (p ∈ E.val ∧ p ∈ F.val) := by
    intro ⟨he, hf⟩
    have hm := Finset.mem_inter.mpr ⟨he, hf⟩
    rw [Finset.card_eq_zero.mp hi] at hm
    simpa using hm
  rw [coordinateCubic_point_octad_bilinear, cubicPointOctadIncidence_overlap_sum, hi]
  have h := congrArg (fun c : golay => c.val p) hF
  simp only [Submodule.coe_add, Pi.add_apply, octadWord_apply, golayOne] at h
  by_cases hDp : p ∈ D.val <;> by_cases hEp : p ∈ E.val <;>
    by_cases hFp : p ∈ F.val <;>
    simp [hDp, hEp, hFp, allOnes, show (2 : Bit) = 0 from rfl] at h hEF <;>
    norm_num [cubicPointOctadIncidence, hDp, hEp, hFp]

end Atlas.Fischer
