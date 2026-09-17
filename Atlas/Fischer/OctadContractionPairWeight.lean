import Atlas.Fischer.OctadContractionWeight

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The actual signed two-free-octad summand. Invalid configurations have zero
weight; every completion in a valid configuration is the retained Golay diamond. -/
def octadContractionPairWeight (D E F G H : Octad) : ℤ :=
  if hGH : OctadPairAdmissible G H then
    if hDG : OctadPairAdmissible D G then
      if hEH : OctadPairAdmissible E H then
        if hFJ : OctadPairAdmissible F (octadDiamond G H hGH) then
          octadContractionIntegerWeight D E F G H (octadDiamond G H hGH)
            (octadDiamond D G hDG) (octadDiamond E H hEH)
        else 0
      else 0
    else 0
  else 0

end Atlas.Fischer
