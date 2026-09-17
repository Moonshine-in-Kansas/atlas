import Atlas.Fischer.OctadDiamondClosure
import Atlas.Fischer.CubicOctadDiamondSupport

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem octadDiamond_eq_of_line (D E F : Octad) (h : OctadPairAdmissible D E)
    (hF : octadWord D + octadWord E + octadWord F ∈ allOneCodeLine) :
    F = octadDiamond D E h := by
  have hc (z : golay) : octadWord D + octadWord E +
      (octadWord D + octadWord E + z) = z := by
    calc
      _ = (octadWord D + octadWord D) + (octadWord E + octadWord E) + z := by abel
      _ = z := by simp only [parkerGolay_add_self, zero_add]
  apply octadDiamond_eq_of_triangle
  rcases (mem_allOneCodeLine _).mp hF with hF | hF
  · left
    simpa only [hc, add_zero] using congrArg (fun z => octadWord D + octadWord E + z) hF
  · right
    simpa only [hc] using congrArg (fun z => octadWord D + octadWord E + z) hF

theorem octad_quadrilateral_triangle_closure (D F G : Octad)
    (hDF : OctadPairAdmissible D F) (hDG : OctadPairAdmissible D G)
    (hFG : OctadPairAdmissible F G) :
    octadWord (octadDiamond D F hDF) + octadWord (octadDiamond D G hDG) +
      octadWord (octadDiamond F G hFG) ∈ allOneCodeLine := by
  have h := allOneCodeLine.add_mem (allOneCodeLine.add_mem
    (octadDiamond_triangle_line D F hDF) (octadDiamond_triangle_line D G hDG))
      (octadDiamond_triangle_line F G hFG)
  convert h using 1
  symm
  calc
    _ = (octadWord D + octadWord D) + (octadWord F + octadWord F) +
        (octadWord G + octadWord G) +
        (octadWord (octadDiamond D F hDF) + octadWord (octadDiamond D G hDG) +
          octadWord (octadDiamond F G hFG)) := by abel
    _ = _ := by simp only [parkerGolay_add_self, zero_add]

theorem octad_quadrilateral_admissible (D F G : Octad)
    (hDF : OctadPairAdmissible D F) (hDG : OctadPairAdmissible D G)
    (hFG : OctadPairAdmissible F G) :
    OctadPairAdmissible (octadDiamond D F hDF) (octadDiamond D G hDG) :=
  octadPairAdmissible_of_line _ _ _ (octad_quadrilateral_triangle_closure D F G hDF hDG hFG)

end Atlas.Fischer
