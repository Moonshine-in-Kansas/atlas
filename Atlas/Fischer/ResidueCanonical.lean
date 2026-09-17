import Atlas.Fischer.ResidueOrder
import Atlas.Fischer.ResiduePointCount

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The canonical markings retain the existing Golay coordinate system. -/
def fischerFirstCoordinate : Omega := ((0,0),0)
def fischerSecondCoordinate : Omega := ((0,0),1)
def fischer23Marking : Finset Omega := {fischerFirstCoordinate}
def fischer22Marking : Finset Omega := {fischerFirstCoordinate,fischerSecondCoordinate}

@[simp] theorem fischer23Marking_card : fischer23Marking.card=1 := by decide
@[simp] theorem fischer22Marking_card : fischer22Marking.card=2 := by decide

end Atlas.Fischer
