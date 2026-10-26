import Atlas.LinearGroups.ReeF4.RootTriangularShortParameter0
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem alternating_short_parameter_strictlyLowering_1 (τ : F →+* F) (a : F) :
    StrictlyLoweringFormula (alternatingShortPermutation 1) (shortRootParameterFormula τ a) := by
  intro w c hzero
  rcases c with ⟨i,j⟩
  fin_cases i <;> fin_cases j
  · -- Coordinate (0,0); 0 genuine higher support coordinates.
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv]
  · -- Coordinate (0,1); 0 genuine higher support coordinates.
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv]
  · -- Coordinate (0,2); 3 genuine higher support coordinates.
    have hz0 := hzero (0,3) (by decide)
    change w.2 0 3 = 0 at hz0
    have hz1 := hzero (0,5) (by decide)
    change w.2 0 4 = 0 at hz1
    have hz2 := hzero (0,6) (by decide)
    change w.2 0 5 = 0 at hz2
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv, hz0, hz1, hz2]
  · -- Coordinate (0,3); 3 genuine higher support coordinates.
    have hz0 := hzero (1,4) (by decide)
    change w.1 1 = 0 at hz0
    have hz1 := hzero (2,4) (by decide)
    change w.1 2 = 0 at hz1
    have hz2 := hzero (0,5) (by decide)
    change w.2 0 4 = 0 at hz2
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv, hz0, hz1, hz2]
  · -- Coordinate (0,4); 0 genuine higher support coordinates.
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv]
  · -- Coordinate (0,5); 1 genuine higher support coordinates.
    have hz0 := hzero (0,6) (by decide)
    change w.2 0 5 = 0 at hz0
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv, hz0]
  · -- Coordinate (0,6); 0 genuine higher support coordinates.
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv]
  · -- Coordinate (0,7); 0 genuine higher support coordinates.
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv]
  · -- Coordinate (0,8); 0 genuine higher support coordinates.
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv]
  · -- Coordinate (1,0); 1 genuine higher support coordinates.
    have hz0 := hzero (1,1) (by decide)
    change w.2 1 1 = 0 at hz0
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv, hz0]
  · -- Coordinate (1,1); 1 genuine higher support coordinates.
    have hz0 := hzero (2,1) (by decide)
    change w.2 2 1 = 0 at hz0
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv, hz0]
  · -- Coordinate (1,2); 3 genuine higher support coordinates.
    have hz0 := hzero (1,3) (by decide)
    change w.2 1 3 = 0 at hz0
    have hz1 := hzero (2,2) (by decide)
    change w.2 2 2 = 0 at hz1
    have hz2 := hzero (2,5) (by decide)
    change w.2 2 4 = 0 at hz2
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv, hz0, hz1, hz2]
  · -- Coordinate (1,3); 0 genuine higher support coordinates.
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv]
  · -- Coordinate (1,4); 2 genuine higher support coordinates.
    have hz0 := hzero (0,5) (by decide)
    change w.2 0 4 = 0 at hz0
    have hz1 := hzero (0,6) (by decide)
    change w.2 0 5 = 0 at hz1
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv, hz0, hz1]
  · -- Coordinate (1,5); 3 genuine higher support coordinates.
    have hz0 := hzero (1,6) (by decide)
    change w.2 1 5 = 0 at hz0
    have hz1 := hzero (2,3) (by decide)
    change w.2 2 3 = 0 at hz1
    have hz2 := hzero (2,6) (by decide)
    change w.2 2 5 = 0 at hz2
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv, hz0, hz1, hz2]
  · -- Coordinate (1,6); 0 genuine higher support coordinates.
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv]
  · -- Coordinate (1,7); 1 genuine higher support coordinates.
    have hz0 := hzero (1,8) (by decide)
    change w.2 1 7 = 0 at hz0
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv, hz0]
  · -- Coordinate (1,8); 1 genuine higher support coordinates.
    have hz0 := hzero (2,8) (by decide)
    change w.2 2 7 = 0 at hz0
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv, hz0]
  · -- Coordinate (2,0); 3 genuine higher support coordinates.
    have hz0 := hzero (1,0) (by decide)
    change w.2 1 0 = 0 at hz0
    have hz1 := hzero (1,1) (by decide)
    change w.2 1 1 = 0 at hz1
    have hz2 := hzero (2,1) (by decide)
    change w.2 2 1 = 0 at hz2
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv, hz0, hz1, hz2]
  · -- Coordinate (2,1); 0 genuine higher support coordinates.
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv]
  · -- Coordinate (2,2); 1 genuine higher support coordinates.
    have hz0 := hzero (2,5) (by decide)
    change w.2 2 4 = 0 at hz0
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv, hz0]
  · -- Coordinate (2,3); 1 genuine higher support coordinates.
    have hz0 := hzero (2,6) (by decide)
    change w.2 2 5 = 0 at hz0
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv, hz0]
  · -- Coordinate (2,4); 2 genuine higher support coordinates.
    have hz0 := hzero (0,5) (by decide)
    change w.2 0 4 = 0 at hz0
    have hz1 := hzero (0,6) (by decide)
    change w.2 0 5 = 0 at hz1
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv, hz0, hz1]
  · -- Coordinate (2,5); 1 genuine higher support coordinates.
    have hz0 := hzero (1,3) (by decide)
    change w.2 1 3 = 0 at hz0
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv, hz0]
  · -- Coordinate (2,6); 1 genuine higher support coordinates.
    have hz0 := hzero (1,6) (by decide)
    change w.2 1 5 = 0 at hz0
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv, hz0]
  · -- Coordinate (2,7); 3 genuine higher support coordinates.
    have hz0 := hzero (1,7) (by decide)
    change w.2 1 6 = 0 at hz0
    have hz1 := hzero (1,8) (by decide)
    change w.2 1 7 = 0 at hz1
    have hz2 := hzero (2,8) (by decide)
    change w.2 2 7 = 0 at hz2
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv, hz0, hz1, hz2]
  · -- Coordinate (2,8); 0 genuine higher support coordinates.
    simp [shortRootParameterFormula, wilsonCoordinatesEquiv]
end Atlas.ReeF4
