import Atlas.Fischer.OctadDiamond
import Atlas.Fischer.CubicCocodeSupport

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem octadDiamond_triangle_line (D E : Octad) (h : OctadPairAdmissible D E) :
    octadWord D + octadWord E + octadWord (octadDiamond D E h) ∈ allOneCodeLine := by
  classical
  rw [octadDiamond_word]
  have hx (x y z : golay) : x + y + (x + y + z) = z := by
    calc
      _ = (x + x) + (y + y) + z := by abel
      _ = z := by simp only [parkerGolay_add_self, zero_add]
  rw [hx]
  by_cases h0 : (D.val ∩ E.val).card = 0
  · simp only [h0, ite_true]
    exact (mem_allOneCodeLine _).mpr (Or.inr rfl)
  · simp only [h0, ite_false]
    exact allOneCodeLine.zero_mem

theorem octadPairAdmissible_of_line (D E F : Octad)
    (h : octadWord D + octadWord E + octadWord F ∈ allOneCodeLine) :
    OctadPairAdmissible D E := by
  have hx (x y z : golay) : x + y + (x + y + z) = z := by
    calc
      _ = (x + x) + (y + y) + z := by abel
      _ = z := by simp only [parkerGolay_add_self, zero_add]
  apply octadPairAdmissible_of_triangle D E F
  rcases (mem_allOneCodeLine _).mp h with h | h
  · left
    have hc := congrArg (fun z => octadWord D + octadWord E + z) h
    simpa only [hx, add_zero] using hc
  · right
    have hc := congrArg (fun z => octadWord D + octadWord E + z) h
    simpa only [hx] using hc

/-- The five prescribed triangles force the sixth. All nine objects remain
actual retained Golay octads. -/
theorem octad_contraction_triangle_closure (D E F G H J G' H' J' : Octad)
    (hDE : octadWord D + octadWord E + octadWord F ∈ allOneCodeLine)
    (hGH : octadWord G + octadWord H + octadWord J ∈ allOneCodeLine)
    (hDG : octadWord D + octadWord G + octadWord G' ∈ allOneCodeLine)
    (hEH : octadWord E + octadWord H + octadWord H' ∈ allOneCodeLine)
    (hFJ : octadWord F + octadWord J + octadWord J' ∈ allOneCodeLine) :
    octadWord G' + octadWord H' + octadWord J' ∈ allOneCodeLine := by
  have h := allOneCodeLine.add_mem (allOneCodeLine.add_mem (allOneCodeLine.add_mem
    (allOneCodeLine.add_mem hDE hGH) hDG) hEH) hFJ
  convert h using 1
  symm
  calc
    _ = (octadWord D + octadWord D) + (octadWord E + octadWord E) +
        (octadWord F + octadWord F) + (octadWord G + octadWord G) +
        (octadWord H + octadWord H) + (octadWord J + octadWord J) +
        (octadWord G' + octadWord H' + octadWord J') := by abel
    _ = _ := by simp only [parkerGolay_add_self, zero_add]

end Atlas.Fischer
