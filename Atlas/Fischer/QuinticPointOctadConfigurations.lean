import Atlas.Fischer.QuinticPointOctadNetwork
import Atlas.Fischer.CubicOctadQuadrilateralEdges

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The purely octadic contribution as a sum over actual three-pair configurations. -/
theorem quinticPointOctadWWW_WWW_configurations (p : Omega) (D : Octad) :
    quinticPointOctadWWW_WWW p D =
      (1 / 16 : Scalar) * ∑ J : Octad, ∑ K : Octad,
        if hDJ : OctadPairAdmissible D J then
          if hDK : OctadPairAdmissible D K then
            if hJK : OctadPairAdmissible J K then
              cubicPointOctadIncidence p (octadDiamond J K hJK) *
                cubicOctadQuadrilateralWeight D J K hDJ hDK hJK
            else 0
          else 0
        else 0 := by
  rw [quinticPointOctadWWW_WWW_network]
  congr 1
  unfold cubicOctadQuadrilateralNetwork
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro K hK
  rw [← cubicOctadQuadrilateral_edge_sum D J K (fun I => cubicPointOctadIncidence p I)]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro B hB
  apply Finset.sum_congr rfl
  intro C hC
  ring

end Atlas.Fischer
