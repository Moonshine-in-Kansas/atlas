import Atlas.Fischer.CubicCanonicalTriangleTransport
import Atlas.Fischer.TensorCoefficientTransport

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Two actual canonical coefficients suffice for all ordered octad triangles.
The rational factor is transported by actual Parker lifts, including their
sign corrections and scalar conjugation. -/
theorem coordinateQuintic_octad_triangle_of_canonical (c : ℚ)
    (hS : coordinateQuintic (.inr countingCanonicalD) (.inr countingCanonicalSextetE)
      (.inr countingCanonicalSextetF) = (c : Scalar) * coordinateCubic (.inr countingCanonicalD)
        (.inr countingCanonicalSextetE) (.inr countingCanonicalSextetF))
    (hT : coordinateQuintic (.inr countingCanonicalD) (.inr countingCanonicalTrioE)
      (.inr countingCanonicalTrioF) = (c : Scalar) * coordinateCubic (.inr countingCanonicalD)
        (.inr countingCanonicalTrioE) (.inr countingCanonicalTrioF))
    (D E F : Octad)
    (h : octadWord F = octadWord D + octadWord E ∨
      octadWord F = octadWord D + octadWord E + golayOne) :
    coordinateQuintic (.inr D) (.inr E) (.inr F) =
      (c : Scalar) * coordinateCubic (.inr D) (.inr E) (.inr F) := by
  rcases h with h | h
  · obtain ⟨g,hD,hE,hF⟩ := cubicSextetTriangle_canonical D E F h
    apply (coordinateQuintic_proportional_mathieu g D E F c).mp
    simpa only [hD,hE,hF] using hS
  · obtain ⟨g,hD,hE,hF⟩ := cubicTrioTriangle_canonical D E F h
    apply (coordinateQuintic_proportional_mathieu g D E F c).mp
    simpa only [hD,hE,hF] using hT

end Atlas.Fischer
