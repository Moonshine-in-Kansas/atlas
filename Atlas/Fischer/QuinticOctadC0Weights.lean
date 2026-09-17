import Atlas.Fischer.QuinticOctadC0Block
import Atlas.Fischer.CubicOctadQuadrilateralEdges

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Multiplication by the external conjugated cubic gives exactly the existing
four-triangle scalar weight, without a phase identification assumption. -/
theorem cubicOctadTriangleNeighbor_weight (D E F H : Octad)
    (hEF : OctadPairAdmissible E F) (hD : D = octadDiamond E F hEF) :
    star (coordinateCubic (.inr D) (.inr E) (.inr F)) *
      cubicOctadTriangleNeighbor D E F H =
      if hHE : OctadPairAdmissible H E then
        if hHF : OctadPairAdmissible H F then
          cubicOctadQuadrilateralWeight H E F hHE hHF hEF else 0 else 0 := by
  have hs := cubicOctadQuadrilateral_edge_sum H E F (fun I => if I = D then (1 : Scalar) else 0)
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, dif_pos hEF,
    hD, ite_true, one_mul] at hs
  rw [← hs]
  unfold cubicOctadTriangleNeighbor
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  apply Finset.sum_congr rfl
  intro C hC
  rw [hD]
  ring

/-- Exact weighted-quadrilateral reduction of one C0 orientation. -/
theorem quinticOctadBlockUWW_WWW_weights (D E F : Octad)
    (hEF : OctadPairAdmissible E F) (hD : D = octadDiamond E F hEF) :
    star (coordinateCubic (.inr D) (.inr E) (.inr F)) *
      quinticOctadBlockUWW_WWW D E F =
      ∑ H : Octad, cubicOctadPointGram D H *
        (if hHE : OctadPairAdmissible H E then
          if hHF : OctadPairAdmissible H F then
            cubicOctadQuadrilateralWeight H E F hHE hHF hEF else 0 else 0) := by
  rw [quinticOctadBlockUWW_WWW_neighbors, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H hH
  rw [mul_left_comm, cubicOctadTriangleNeighbor_weight D E F H hEF hD]

end Atlas.Fischer
