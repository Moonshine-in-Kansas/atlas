import Atlas.Rudvalis.FrameGlueIdentification
import Atlas.Rudvalis.SeedCoordinates

/-! The literal six-position orbit generator for the Frobenius-stable glue line. -/
namespace Atlas.Rudvalis

def frameGlueHexad : FrameGlueWord := fun z =>
  if z.2=binaryLabel (![5,0,1] z.1) ∨ z.2=binaryLabel (![6,3,2] z.1) then 1 else 0

def frameGlueHexadParameters : FrameGlueParameters :=
  (![0,1,0],![binaryLabel 7,binaryLabel 4],binaryLabel 3)

theorem frameGlueHexad_normal : frameGlueHexad=frameGlueNormalMap frameGlueHexadParameters := by
  funext z
  decide +kernel +revert

theorem frameGlueHexad_mem : frameGlueHexad∈frameGlueCode :=
  ⟨frameGlueHexadParameters,frameGlueHexad_normal.symm⟩

theorem frameGlueHexad_torsion : frameGlueExtension frameGlueHexad∈binaryTorsion :=
  (frameGlueCode_shortening _).mpr frameGlueHexad_mem

theorem frameGlueHexad_weight : hammingNorm frameGlueHexad=6 := by decide +kernel

/-- Actual original real row indices of the three local blocks. -/
def frameGlueRow (i : Fin 3) : Fin 7 := ![1,2,4] i

theorem frameGluePoint_row (i : Fin 3) : frameGluePoint i=rowLabel (frameGlueRow i) := by
  decide +kernel +revert

/-- In the original e0,...,e7 position order the selected pairs are (5,6),(1,3),(3,5). -/
theorem frameGlueHexad_real_positions (i : Fin 3) (k : Fin 8) :
    frameGlueHexad (i,seedInnerLabel (frameGlueRow i) (signedPositionIndex k))=
      if k=(![5,1,3] i) ∨ k=(![6,3,5] i) then 1 else 0 := by
  decide +kernel +revert

end Atlas.Rudvalis
