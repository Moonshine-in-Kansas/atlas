import Atlas.LinearGroups.ReeF4.SpecialAdjoint
import Atlas.LinearGroups.ReeF4.SpecialSecondPivotVanishing

noncomputable section
namespace Atlas.ReeF4
/-- Wilson's absolute grades in the explicitly retained marked coordinates. -/
def specialAbsoluteGrade : Fin 26 → ℤ := ![0,0,-12,-6,-4,-2,2,4,6,12,-10,-9,-7,-1,1,7,9,10,-11,-8,-5,3,-3,5,8,11]
end Atlas.ReeF4
