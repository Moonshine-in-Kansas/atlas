import Atlas.Fischer.OctadicRootMapHyperplane
import Atlas.Fischer.OctadicNineBlock

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The actual signed axis vector w_b from source (5.13). -/
def octadicHyperplaneAxisVector {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) : Coordinates :=
  (2 : Scalar) • octadicHyperplaneAxisSum Q b - octadExteriorAxisSum O

theorem hermitian_axis_finset_sums (A B : Finset Omega) :
    hermitian (∑ i ∈ A, u i) (∑ j ∈ B, u j) = ((A ∩ B).card : Scalar) / 8 := by
  simp only [hermitian_sum_left, hermitian_sum_right, hermitian_u, Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    Finset.filter_mem_eq_inter, Finset.inter_comm, nsmul_eq_mul]
  ring

theorem octadExteriorAxisSum_norm (O : Octad) :
    hermitian (octadExteriorAxisSum O) (octadExteriorAxisSum O) = 2 := by
  rw [octadExteriorAxisSum, hermitian_axis_finset_sums, Finset.inter_self, Finset.card_compl]
  have hc : Fintype.card Omega = 24 := by decide
  rw [hc, octad_size O.val O.property]
  norm_num

theorem hermitian_hyperplaneAxis_exterior {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    hermitian (octadicHyperplaneAxisSum Q b) (octadExteriorAxisSum O) = 1 := by
  rw [octadicHyperplaneAxisSum, octadAxisSum, octadExteriorAxisSum,
    hermitian_axis_finset_sums]
  have hs : (signedOctadSupport (calibratedHyperplaneLift Q b)).val ⊆ O.valᶜ := by
    intro i hi
    exact Finset.mem_compl.mpr (fun h =>
      Finset.disjoint_left.mp (calibratedHyperplaneSupport_disjoint Q b) h hi)
  rw [Finset.inter_eq_left.mpr hs, octad_size _ (signedOctadSupport _).property]
  norm_num

theorem hermitian_exterior_hyperplaneAxis {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) :
    hermitian (octadExteriorAxisSum O) (octadicHyperplaneAxisSum Q b) = 1 := by
  rw [← hermitian_star, hermitian_hyperplaneAxis_exterior, star_one]

private theorem twice_shortened (O : Octad) (b : octadShortenedCode O) : b + b = 0 := by
  rw [← two_smul Bit, show (2 : Bit) = 0 from rfl, zero_smul]

theorem calibratedHyperplane_intersection_cases {O : Octad} (Q : OctadCalibration O)
    (b c : OctadShortenedHyperplane O) :
    signedOctadIntersection (calibratedHyperplaneLift Q b) (calibratedHyperplaneLift Q c) =
      if b = c then 8 else if c = octadHyperplaneComplement O b then 0 else 4 := by
  by_cases hbc : b = c
  · subst c
    simp only [signedOctadIntersection, Finset.inter_self, ite_true]
    exact octad_size _ (signedOctadSupport _).property
  · rw [ite_eq_right hbc]
    by_cases hc : c = octadHyperplaneComplement O b
    · rw [ite_eq_left hc]
      apply calibrated_hyperplanes_disjoint Q b c
      rw [hc]
      change b.val + (b.val + octadShortenedOne O) = octadShortenedOne O
      rw [← add_assoc, twice_shortened, zero_add]
    · rw [ite_eq_right hc]
      have hz : b.val + c.val ≠ 0 := by
        intro h
        apply hbc
        apply Subtype.ext
        have hh := congrArg (fun a : octadShortenedCode O => a + c.val) h
        simpa only [add_assoc, twice_shortened, add_zero, zero_add] using hh
      have hX : b.val + c.val ≠ octadShortenedOne O := by
        intro h
        apply hc
        apply Subtype.ext
        have hh := congrArg (fun a : octadShortenedCode O => b.val + a) h
        simpa only [← add_assoc, twice_shortened, zero_add, octadHyperplaneComplement] using hh
      exact calibrated_hyperplanes_intersection_four Q b c ⟨b.val+c.val, hz, hX⟩ rfl

theorem hermitian_hyperplaneAxisVector {O : Octad} (Q : OctadCalibration O)
    (b c : OctadShortenedHyperplane O) :
    hermitian (octadicHyperplaneAxisVector Q b) (octadicHyperplaneAxisVector Q c) =
      if b = c then 2 else if c = octadHyperplaneComplement O b then -2 else 0 := by
  have hbc : hermitian (octadicHyperplaneAxisSum Q b) (octadicHyperplaneAxisSum Q c) =
      (signedOctadIntersection (calibratedHyperplaneLift Q b)
        (calibratedHyperplaneLift Q c) : Scalar) / 8 := by
    exact hermitian_axis_finset_sums _ _
  simp only [octadicHyperplaneAxisVector, hermitian_sub_left, hermitian_sub_right,
    hermitian_smul_left, hermitian_smul_right, hbc, hermitian_hyperplaneAxis_exterior,
    hermitian_exterior_hyperplaneAxis, octadExteriorAxisSum_norm, star_ofNat]
  rw [calibratedHyperplane_intersection_cases]
  split_ifs <;> norm_num

end Atlas.Fischer
